/*

  Reference Cycle Garbage Collection
  ==================================

  Neil Schemenauer <nas@arctrix.com>

  Based on a post on the python-dev list.  Ideas from Guido van Rossum,
  Eric Tiedemann, and various others.

  http://www.arctrix.com/nas/python/gc/
  http://www.python.org/pipermail/python-dev/2000-March/003869.html
  http://www.python.org/pipermail/python-dev/2000-March/004010.html
  http://www.python.org/pipermail/python-dev/2000-March/004022.html

  For a highlevel view of the collection process, read the collect
  function.

*/

#include "Python.h"
#include "frameobject.h"	/* for PyFrame_ClearFreeList */

//#include <list>
#include <ext/hash_map>
#include <stack>

#include <sys/time.h>
#include <hash_set>
using namespace __gnu_cxx;
using namespace std;

/* Get an object's GC head */
#define AS_GC(o) ((PyGC_Head *)(o)-1)

/* Get the object given the GC head */
#define FROM_GC(g) ((PyObject *)(((PyGC_Head *)g)+1))

/*** Global GC state ***/

//#define LOCK(arg) pthread_spin_lock(&arg);
//#define UNLOCK(arg) pthread_spin_unlock(&arg);

struct gc_generation {
	PyGC_Head head;
	int threshold; /* collection threshold */
	int count; /* count of allocations or collections of younger
		      generations */
};


#define NUM_GENERATIONS 3
#define GEN_HEAD(n) (&generations[n].head)

/* linked lists of container objects */
static struct gc_generation generations[NUM_GENERATIONS] = {
	/* PyGC_Head,				threshold,	count */
	{{{GEN_HEAD(0), GEN_HEAD(0), &accgc_white}},	700,		0},
	{{{GEN_HEAD(1), GEN_HEAD(1), &accgc_white}},	10,		0},
	{{{GEN_HEAD(2), GEN_HEAD(2), &accgc_white}},	10,		0},
};

struct hash_Object{
	size_t operator()(PyObject* const&x)const{
		return ((size_t)x) >> 5;
	}
};
#define in(accgc_roots, obj) accgc_roots.find(obj) != accgc_roots.end()
typedef hash_set<PyObject*, hash_Object > obj_set;
PyGC_Head* p_accgc_white;
PyGC_Head* p_accgc_gray;
PyGC_Head* p_accgc_black;
PyGC_Head* p_accgc_root;
PyGC_Head* p_accgc_delete;
int white_list;
PyGC_Head gc_lists[3];
PyGC_Head accgc_white;
PyGC_Head accgc_gray;
PyGC_Head accgc_black;
PyGC_Head accgc_root;
PyGC_Head accgc_delete;
obj_set accgc_roots;
int accgc_run = 0;
int accgc_enable = 0;
int accgc_main_thread = 0;

SPINLOCK(colored_lock);
//pthread_spinlock_t colored_lock;
//pthread_mutex_t colored_mutex = PTHREAD_MUTEX_INITIALIZER;

int pshared;
#define COL_HEAD(n) (&colored[n])
/* linked lists of container objects */
PyGC_Head colored[3] = {
	{{COL_HEAD(0), COL_HEAD(0), 0}},
	{{COL_HEAD(1), COL_HEAD(1), 0}},
	{{COL_HEAD(2), COL_HEAD(2), 0}},
};

PyGC_Head *_PyGC_generation0 = GEN_HEAD(0);
PyGC_Head *_PyGC_gray = COL_HEAD(0);

static int enabled = 1; /* automatic collection enabled? */

/* true if we are currently running the collector */
static int collecting = 0;

/* list of uncollectable objects */
static PyObject *garbage = NULL;

/* Python string to use if unhandled exception occurs */
static PyObject *gc_str = NULL;

/* Python string used to look for __del__ attribute. */
static PyObject *delstr = NULL;

/* set for debugging information */
#define DEBUG_STATS		(1<<0) /* print collection statistics */
#define DEBUG_COLLECTABLE	(1<<1) /* print collectable objects */
#define DEBUG_UNCOLLECTABLE	(1<<2) /* print uncollectable objects */
#define DEBUG_INSTANCES		(1<<3) /* print instances */
#define DEBUG_OBJECTS		(1<<4) /* print other objects */
#define DEBUG_SAVEALL		(1<<5) /* save all garbage in gc.garbage */
#define DEBUG_LEAK		DEBUG_COLLECTABLE | \
				DEBUG_UNCOLLECTABLE | \
				DEBUG_INSTANCES | \
				DEBUG_OBJECTS | \
				DEBUG_SAVEALL
static int debug;
static PyObject *tmod = NULL;

#define GC_UNTRACKED			_PyGC_REFS_UNTRACKED
#define GC_REACHABLE			_PyGC_REFS_REACHABLE
#define GC_TENTATIVELY_UNREACHABLE	_PyGC_REFS_TENTATIVELY_UNREACHABLE

/* performance measure */


#ifdef PERF
stack<struct timeval> time_stack;

inline void perf_start(){
	struct timeval tv;
	gettimeofday(&tv, NULL);
	time_stack.push(tv);
}

inline void perf_stop(const char*str){
	struct timeval tv; 
	int i = time_stack.size();
	gettimeofday(&tv, NULL);
	while(i--)
		_eprintf(" ");
	_eprintf("Perf time (%s): %d us\n", str, (tv).tv_usec - time_stack.top().tv_usec +
			1000000 * ((tv).tv_sec - time_stack.top().tv_sec));
	time_stack.pop();
}
inline void perf_stop(){
	perf_stop("");
}
inline void perf_inter(const char*str){
	struct timeval tv; 
	int i = time_stack.size();
	gettimeofday(&tv, NULL);
	while(i--)
		_eprintf(" ");
	_eprintf("Perf time (%s): %d us\n", str, (tv).tv_usec - time_stack.top().tv_usec +
			1000000 * ((tv).tv_sec - time_stack.top().tv_sec));
	time_stack.pop();
	time_stack.push(tv);
}
inline void perf_inter(){
	perf_inter("");
}
#else
#define perf_start()
#define perf_stop()
#define perf_stop(arg)
#define perf_inter()
#define perf_inter(arg)
#endif


/*** list functions ***/

static void
gc_list_init(PyGC_Head *list)
{
	list->gc.gc_prev = list;
	list->gc.gc_next = list;
}

static int
gc_list_is_empty(PyGC_Head *list)
{
	return (list->gc.gc_next == list);
}

#if 0
/* This became unused after gc_list_move() was introduced. */
/* Append `node` to `list`. */
static void
gc_list_append(PyGC_Head *node, PyGC_Head *list)
{
	node->gc.gc_next = list;
	node->gc.gc_prev = list->gc.gc_prev;
	node->gc.gc_prev->gc.gc_next = node;
	list->gc.gc_prev = node;
}
#endif

/* Remove `node` from the gc list it's currently in. */
static void
gc_list_remove(PyGC_Head *node)
{
	node->gc.gc_prev->gc.gc_next = node->gc.gc_next;
	node->gc.gc_next->gc.gc_prev = node->gc.gc_prev;
	node->gc.gc_next = NULL; /* object is not currently tracked */
}

/* Move `node` from the gc list it's currently in (which is not explicitly
 * named here) to the end of `list`.  This is semantically the same as
 * gc_list_remove(node) followed by gc_list_append(node, list).
 */
static void
gc_list_move(PyGC_Head *node, PyGC_Head *list)
{
	PyGC_Head *new_prev;
	PyGC_Head *current_prev = node->gc.gc_prev;
	PyGC_Head *current_next = node->gc.gc_next;
	/* Unlink from current list. */
	current_prev->gc.gc_next = current_next;
	current_next->gc.gc_prev = current_prev;
	/* Relink at end of new list. */
	new_prev = node->gc.gc_prev = list->gc.gc_prev;
	new_prev->gc.gc_next = list->gc.gc_prev = node;
	node->gc.gc_next = list;
}

/* append list `from` onto list `to`; `from` becomes an empty list */
static void
gc_list_merge(PyGC_Head *from, PyGC_Head *to)
{
	PyGC_Head *tail;
	assert(from != to);
	if (!gc_list_is_empty(from)) {
		tail = to->gc.gc_prev;
		tail->gc.gc_next = from->gc.gc_next;
		tail->gc.gc_next->gc.gc_prev = tail;
		to->gc.gc_prev = from->gc.gc_prev;
		to->gc.gc_prev->gc.gc_next = to;
	}
	gc_list_init(from);
}

static Py_ssize_t
gc_list_size(PyGC_Head *list)
{
	PyGC_Head *gc;
	Py_ssize_t n = 0;
	for (gc = list->gc.gc_next; gc != list; gc = gc->gc.gc_next) {
		n++;
	}
	return n;
}

/* Append objects in a GC list to a Python list.
 * Return 0 if all OK, < 0 if error (out of memory for list).
 */
static int
append_objects(PyObject *py_list, PyGC_Head *gc_list)
{
	PyGC_Head *gc;
	for (gc = gc_list->gc.gc_next; gc != gc_list; gc = gc->gc.gc_next) {
		PyObject *op = FROM_GC(gc);
		if (op != py_list) {
			if (PyList_Append(py_list, op)) {
				return -1; /* exception */
			}
		}
	}
	return 0;
}

/*** end of list stuff ***/


/* Clear all free lists
 * All free lists are cleared during the collection of the highest generation.
 * Allocated items in the free list may keep a pymalloc arena occupied.
 * Clearing the free lists may give back memory to the OS earlier.
 */
static void
clear_freelists(void)
{
	(void)PyMethod_ClearFreeList();
	(void)PyFrame_ClearFreeList();
	(void)PyCFunction_ClearFreeList();
	(void)PyTuple_ClearFreeList();
	(void)PyUnicode_ClearFreeList();
	(void)PyInt_ClearFreeList();
	(void)PyFloat_ClearFreeList();
}

static double
get_time(void)
{
	double result = 0;
	if (tmod != NULL) {
		PyObject *f = PyObject_CallMethod(tmod, "time", NULL);
		if (f == NULL) {
			PyErr_Clear();
		}
		else {
			if (PyFloat_Check(f))
				result = PyFloat_AsDouble(f);
			Py_DECREF(f);
		}
	}
	return result;
}

static Py_ssize_t
collect_generations(void)
{
	int i;
	Py_ssize_t n = 0;
	return n;
}

PyDoc_STRVAR(gc_enable__doc__,
"enable() -> None\n"
"\n"
"Enable automatic garbage collection.\n");

static PyObject *
gc_enable(PyObject *self, PyObject *noargs)
{
	enabled = 1;
	Py_INCREF(Py_None);
	return Py_None;
}

PyDoc_STRVAR(gc_disable__doc__,
"disable() -> None\n"
"\n"
"Disable automatic garbage collection.\n");

static PyObject *
gc_disable(PyObject *self, PyObject *noargs)
{
	enabled = 0;
	Py_INCREF(Py_None);
	return Py_None;
}

PyDoc_STRVAR(gc_isenabled__doc__,
"isenabled() -> status\n"
"\n"
"Returns true if automatic garbage collection is enabled.\n");

static PyObject *
gc_isenabled(PyObject *self, PyObject *noargs)
{
	return PyBool_FromLong((long)enabled);
}

PyDoc_STRVAR(gc_collect__doc__,
"collect([generation]) -> n\n"
"\n"
"With no arguments, run a full collection.  The optional argument\n"
"may be an integer specifying which generation to collect.  A ValueError\n"
"is raised if the generation number is invalid.\n\n"
"The number of unreachable objects is returned.\n");

static PyObject *
gc_collect(PyObject *self, PyObject *args, PyObject *kws){
	Py_ssize_t n = 0;
	return PyInt_FromSsize_t(n);
}

PyDoc_STRVAR(gc_set_debug__doc__,
"set_debug(flags) -> None\n"
"\n"
"Set the garbage collection debugging flags. Debugging information is\n"
"written to sys.stderr.\n"
"\n"
"flags is an integer and can have the following bits turned on:\n"
"\n"
"  DEBUG_STATS - Print statistics during collection.\n"
"  DEBUG_COLLECTABLE - Print collectable objects found.\n"
"  DEBUG_UNCOLLECTABLE - Print unreachable but uncollectable objects found.\n"
"  DEBUG_INSTANCES - Print instance objects.\n"
"  DEBUG_OBJECTS - Print objects other than instances.\n"
"  DEBUG_SAVEALL - Save objects to gc.garbage rather than freeing them.\n"
"  DEBUG_LEAK - Debug leaking programs (everything but STATS).\n");

static PyObject *
gc_set_debug(PyObject *self, PyObject *args)
{
	if (!PyArg_ParseTuple(args, "i:set_debug", &debug))
		return NULL;

	Py_INCREF(Py_None);
	return Py_None;
}

PyDoc_STRVAR(gc_get_debug__doc__,
"get_debug() -> flags\n"
"\n"
"Get the garbage collection debugging flags.\n");

static PyObject *
gc_get_debug(PyObject *self, PyObject *noargs)
{
	return Py_BuildValue("i", debug);
}

PyDoc_STRVAR(gc_set_thresh__doc__,
"set_threshold(threshold0, [threshold1, threshold2]) -> None\n"
"\n"
"Sets the collection thresholds.  Setting threshold0 to zero disables\n"
"collection.\n");

static PyObject *
gc_set_thresh(PyObject *self, PyObject *args)
{
	int i;
	if (!PyArg_ParseTuple(args, "i|ii:set_threshold",
			      &generations[0].threshold,
			      &generations[1].threshold,
			      &generations[2].threshold))
		return NULL;
	for (i = 2; i < NUM_GENERATIONS; i++) {
 		/* generations higher than 2 get the same threshold */
		generations[i].threshold = generations[2].threshold;
	}

	Py_INCREF(Py_None);
	return Py_None;
}

PyDoc_STRVAR(gc_get_thresh__doc__,
"get_threshold() -> (threshold0, threshold1, threshold2)\n"
"\n"
"Return the current collection thresholds\n");

static PyObject *
gc_get_thresh(PyObject *self, PyObject *noargs)
{
	return Py_BuildValue("(iii)",
			     generations[0].threshold,
			     generations[1].threshold,
			     generations[2].threshold);
}

PyDoc_STRVAR(gc_get_count__doc__,
"get_count() -> (count0, count1, count2)\n"
"\n"
"Return the current collection counts\n");

static PyObject *
gc_get_count(PyObject *self, PyObject *noargs)
{
	return Py_BuildValue("(iii)",
			     generations[0].count,
			     generations[1].count,
			     generations[2].count);
}

static int
referrersvisit(PyObject* obj, PyObject *objs)
{
	Py_ssize_t i;
	for (i = 0; i < PyTuple_GET_SIZE(objs); i++)
		if (PyTuple_GET_ITEM(objs, i) == obj)
			return 1;
	return 0;
}

static int
gc_referrers_for(PyObject *objs, PyGC_Head *list, PyObject *resultlist)
{
	PyGC_Head *gc;
	PyObject *obj;
	traverseproc traverse;
	for (gc = list->gc.gc_next; gc != list; gc = gc->gc.gc_next) {
		obj = FROM_GC(gc);
		traverse = Py_TYPE(obj)->tp_traverse;
		if (obj == objs || obj == resultlist)
			continue;
		if (traverse(obj, (visitproc)referrersvisit, objs)) {
			if (PyList_Append(resultlist, obj) < 0)
				return 0; /* error */
		}
	}
	return 1; /* no error */
}

PyDoc_STRVAR(gc_get_referrers__doc__,
"get_referrers(*objs) -> list\n\
Return the list of objects that directly refer to any of objs.");

static PyObject *
gc_get_referrers(PyObject *self, PyObject *args)
{
	int i;
	PyObject *result = PyList_New(0);
	if (!result) return NULL;

	for (i = 0; i < NUM_GENERATIONS; i++) {
		if (!(gc_referrers_for(args, GEN_HEAD(i), result))) {
			Py_DECREF(result);
			return NULL;
		}
	}
	return result;
}

/* Append obj to list; return true if error (out of memory), false if OK. */
static int
referentsvisit(PyObject *obj, PyObject *list)
{
	return PyList_Append(list, obj) < 0;
}

PyDoc_STRVAR(gc_get_referents__doc__,
"get_referents(*objs) -> list\n\
Return the list of objects that are directly referred to by objs.");

static PyObject *
gc_get_referents(PyObject *self, PyObject *args)
{
	Py_ssize_t i;
	PyObject *result = PyList_New(0);

	if (result == NULL)
		return NULL;

	for (i = 0; i < PyTuple_GET_SIZE(args); i++) {
		traverseproc traverse;
		PyObject *obj = PyTuple_GET_ITEM(args, i);

		if (! PyObject_IS_GC(obj))
			continue;
		traverse = Py_TYPE(obj)->tp_traverse;
		if (! traverse)
			continue;
		if (traverse(obj, (visitproc)referentsvisit, result)) {
			Py_DECREF(result);
			return NULL;
		}
	}
	return result;
}

PyDoc_STRVAR(gc_get_objects__doc__,
"get_objects() -> [...]\n"
"\n"
"Return a list of objects tracked by the collector (excluding the list\n"
"returned).\n");

static PyObject *
gc_get_objects(PyObject *self, PyObject *noargs)
{
	int i;
	PyObject* result;

	result = PyList_New(0);
	if (result == NULL)
		return NULL;
	for (i = 0; i < NUM_GENERATIONS; i++) {
		if (append_objects(result, GEN_HEAD(i))) {
			Py_DECREF(result);
			return NULL;
		}
	}
	return result;
}


PyDoc_STRVAR(gc__doc__,
"This module provides access to the garbage collector for reference cycles.\n"
"\n"
"enable() -- Enable automatic garbage collection.\n"
"disable() -- Disable automatic garbage collection.\n"
"isenabled() -- Returns true if automatic collection is enabled.\n"
"collect() -- Do a full collection right now.\n"
"get_count() -- Return the current collection counts.\n"
"set_debug() -- Set debugging flags.\n"
"get_debug() -- Get debugging flags.\n"
"set_threshold() -- Set the collection thresholds.\n"
"get_threshold() -- Return the current the collection thresholds.\n"
"get_objects() -- Return a list of all objects tracked by the collector.\n"
"get_referrers() -- Return the list of objects that refer to an object.\n"
"get_referents() -- Return the list of objects that an object refers to.\n");

static PyMethodDef GcMethods[] = {
	{"enable",	   gc_enable,	  METH_NOARGS,  gc_enable__doc__},
	{"disable",	   gc_disable,	  METH_NOARGS,  gc_disable__doc__},
	{"isenabled",	   gc_isenabled,  METH_NOARGS,  gc_isenabled__doc__},
	{"set_debug",	   gc_set_debug,  METH_VARARGS, gc_set_debug__doc__},
	{"get_debug",	   gc_get_debug,  METH_NOARGS,  gc_get_debug__doc__},
	{"get_count",	   gc_get_count,  METH_NOARGS,  gc_get_count__doc__},
	{"set_threshold",  gc_set_thresh, METH_VARARGS, gc_set_thresh__doc__},
	{"get_threshold",  gc_get_thresh, METH_NOARGS,  gc_get_thresh__doc__},
	{"collect",	   (PyCFunction)gc_collect,
         	METH_VARARGS | METH_KEYWORDS,           gc_collect__doc__},
	{"get_objects",    gc_get_objects,METH_NOARGS,  gc_get_objects__doc__},
	{"get_referrers",  gc_get_referrers, METH_VARARGS,
		gc_get_referrers__doc__},
	{"get_referents",  gc_get_referents, METH_VARARGS,
		gc_get_referents__doc__},
	{NULL,	NULL}		/* Sentinel */
};

PyMODINIT_FUNC
initgc(void)
{
	PyObject *m;

	m = Py_InitModule4("gc",
			      GcMethods,
			      gc__doc__,
			      NULL,
			      PYTHON_API_VERSION);
	if (m == NULL)
		return;

	if (garbage == NULL) {
		garbage = PyList_New(0);
		if (garbage == NULL)
			return;
	}
	Py_INCREF(garbage);
	if (PyModule_AddObject(m, "garbage", garbage) < 0)
		return;

	/* Importing can't be done in collect() because collect()
	 * can be called via PyGC_Collect() in Py_Finalize().
	 * This wouldn't be a problem, except that <initialized> is
	 * reset to 0 before calling collect which trips up
	 * the import and triggers an assertion.
	 */
	if (tmod == NULL) {
		tmod = PyImport_ImportModuleNoBlock("time");
		if (tmod == NULL)
			PyErr_Clear();
	}
	pshared = PTHREAD_PROCESS_PRIVATE;
#define ADD_INT(NAME) if (PyModule_AddIntConstant(m, #NAME, NAME) < 0) return
	ADD_INT(DEBUG_STATS);
	ADD_INT(DEBUG_COLLECTABLE);
	ADD_INT(DEBUG_UNCOLLECTABLE);
	ADD_INT(DEBUG_INSTANCES);
	ADD_INT(DEBUG_OBJECTS);
	ADD_INT(DEBUG_SAVEALL);
	ADD_INT(DEBUG_LEAK);
#undef ADD_INT
}

/* API to invoke gc.collect() from C */
Py_ssize_t
PyGC_Collect(void)
{
	Py_ssize_t n = 0;
	return n;
}

/* for debugging */
void
_PyGC_Dump(PyGC_Head *g)
{
	_PyObject_Dump(FROM_GC(g));
}

/* extension modules might be compiled with GC support so these
   functions must always be available */

#undef PyObject_GC_Del
#undef _PyObject_GC_Malloc


/* for binary compatibility with 2.2 */
void
_PyObject_GC_Track(PyObject *op)
{
    PyObject_GC_Track(op);
}

/* for binary compatibility with 2.2 */
void
_PyObject_GC_UnTrack(PyObject *op)
{
    PyObject_GC_UnTrack(op);
}

struct eqstr
{
  bool operator()(const char* s1, const char* s2) const
  {
    return strcmp(s1, s2) == 0;
  }
};

int alloc_count = 0;
int dealloc_count = 0;
typedef hash_map<const char*, int, hash<const char*>, eqstr> t_types_map;
#ifdef ACCGC_COUNT_TYPES
t_types_map types;
#endif
#ifdef ACCGC_COUNTERS
int failed = 0;
int move_to_black;
#endif
//typedef stack<const char*> t_gc_stack;
//t_gc_stack gc_stack;

int accgc_move_to_list(PyObject *obj, void * list){
	PyGC_Head * head = AS_GC(obj);
	traverseproc traverse;
	int tr_res;
	
	if (!obj)
		return 0;
	
	if(in(accgc_roots, obj))
		return 0;
	
	if(head->gc.gc_next){
#ifdef ACCGC_COUNTERS
		const char* tp_name = obj->ob_type->tp_name;
		if(head->gc.color == p_accgc_delete){
			failed++;
			eprintf("Failed object %p of type %s", obj, tp_name);
		}
#endif
		if(head->gc.color == p_accgc_white){
			traverse = obj->ob_type->tp_traverse;
			if (traverse!=0){
#ifdef ACCGC_COUNT_TYPES
				if(types.count(tp_name) == 0)
					types[tp_name] = 1;
				else
					types[tp_name] = types[tp_name]+1;
#endif
				gc_list_move(head, p_accgc_gray);
				head->gc.color = p_accgc_gray;
				tr_res = traverse(obj,
						(visitproc)accgc_move_to_list,
						p_accgc_black);
			}
#ifdef ACCGC_COUNTERS
			move_to_black++;
#endif
			gc_list_move(head, p_accgc_black);
			head->gc.color = p_accgc_black;
		}else{
			
		}
		
	}else{
		//printf("Object %p of type %s not under GC control!\n", head, obj->ob_type->tp_name);
	}
	return 0;
}

void accgc_list_cycle(){
	white_list += 2;
	white_list %= 3;
	p_accgc_white = &(gc_lists[white_list]);
	p_accgc_gray = &(gc_lists[(white_list+1)%3]);
	p_accgc_black = &(gc_lists[(white_list+2)%3]);
}

void traverse_obj(PyObject* obj, visitproc proc){
	traverseproc traverse = obj->ob_type->tp_traverse;
	if(obj->ob_type->tp_traverse)
		traverse(obj, proc, p_accgc_black);
}

/*
 * Moves objct to root objects list. These objects are start points for GC.
 */
void accgc_to_root(PyObject* obj){
	if(obj)
		accgc_roots.insert(obj);
}

/*
 * Remove object from root objects list. In most cases, this object is no longer used.
 */
void accgc_from_root(PyObject* obj){
	if(obj)
		accgc_roots.erase(obj);
}

#define exp_point(exp) (PyExc_ ## exp)
#define TRAV_OBJ(obj) traverse_obj((PyObject *)(obj), accgc_move_to_list);
#define TRAV_EXC_OBJ(obj) TRAV_OBJ(exp_point(obj));

void accgc_collect_exceptions(){
	TRAV_EXC_OBJ(BaseException)
	TRAV_EXC_OBJ(Exception)
	TRAV_EXC_OBJ(StandardError)
	TRAV_EXC_OBJ(TypeError)
	TRAV_EXC_OBJ(StopIteration)
	TRAV_EXC_OBJ(GeneratorExit)
	TRAV_EXC_OBJ(SystemExit)
	TRAV_EXC_OBJ(KeyboardInterrupt)
	TRAV_EXC_OBJ(ImportError)
	TRAV_EXC_OBJ(EnvironmentError)
	TRAV_EXC_OBJ(IOError)
	TRAV_EXC_OBJ(OSError)
#ifdef MS_WINDOWS
	TRAV_EXC_OBJ(WindowsError)
#endif
#ifdef __VMS
	TRAV_EXC_OBJ(VMSError)
#endif
	TRAV_EXC_OBJ(EOFError)
	TRAV_EXC_OBJ(RuntimeError)
	TRAV_EXC_OBJ(NotImplementedError)
	TRAV_EXC_OBJ(NameError)
	TRAV_EXC_OBJ(UnboundLocalError)
	TRAV_EXC_OBJ(AttributeError)
	TRAV_EXC_OBJ(SyntaxError)
	TRAV_EXC_OBJ(IndentationError)
	TRAV_EXC_OBJ(TabError)
	TRAV_EXC_OBJ(LookupError)
	TRAV_EXC_OBJ(IndexError)
	TRAV_EXC_OBJ(KeyError)
	TRAV_EXC_OBJ(ValueError)
	TRAV_EXC_OBJ(UnicodeError)
#ifdef Py_USING_UNICODE
	TRAV_EXC_OBJ(UnicodeEncodeError)
	TRAV_EXC_OBJ(UnicodeDecodeError)
	TRAV_EXC_OBJ(UnicodeTranslateError)
#endif
	TRAV_EXC_OBJ(AssertionError)
	TRAV_EXC_OBJ(ArithmeticError)
	TRAV_EXC_OBJ(FloatingPointError)
	TRAV_EXC_OBJ(OverflowError)
	TRAV_EXC_OBJ(ZeroDivisionError)
	TRAV_EXC_OBJ(SystemError)
	TRAV_EXC_OBJ(ReferenceError)
	TRAV_EXC_OBJ(MemoryError)
	TRAV_EXC_OBJ(BufferError)
	TRAV_EXC_OBJ(Warning)
	TRAV_EXC_OBJ(UserWarning)
	TRAV_EXC_OBJ(DeprecationWarning)
	TRAV_EXC_OBJ(PendingDeprecationWarning)
	TRAV_EXC_OBJ(SyntaxWarning)
	TRAV_EXC_OBJ(RuntimeWarning)
	TRAV_EXC_OBJ(FutureWarning)
	TRAV_EXC_OBJ(ImportWarning)
	TRAV_EXC_OBJ(UnicodeWarning)
	TRAV_EXC_OBJ(BytesWarning)
}

void accgc_collect_types(){
	/* Basic types */
	//traverse_obj((PyObject *)&PyType_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&_PyWeakref_RefType, accgc_move_to_list);
	traverse_obj((PyObject *)&_PyWeakref_CallableProxyType, accgc_move_to_list);
	traverse_obj((PyObject *)&_PyWeakref_ProxyType, accgc_move_to_list);
	traverse_obj((PyObject *)&PyBool_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyString_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyByteArray_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyList_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyNone_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyNotImplemented_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyTraceBack_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PySuper_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyBaseObject_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyRange_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyDict_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PySet_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyUnicode_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PySlice_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyStaticMethod_Type, accgc_move_to_list);
	#ifndef WITHOUT_COMPLEX
	traverse_obj((PyObject *)&PyComplex_Type, accgc_move_to_list);
	#endif
	traverse_obj((PyObject *)&PyFloat_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyBuffer_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyLong_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyInt_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyFrozenSet_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyProperty_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyTuple_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyEnum_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyReversed_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyCode_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyFrame_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyCFunction_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyMethod_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyFunction_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyClass_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyDictProxy_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyGen_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyGetSetDescr_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyWrapperDescr_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyInstance_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyEllipsis_Type, accgc_move_to_list);
	traverse_obj((PyObject *)&PyMemberDescr_Type, accgc_move_to_list);
}

void accgc_collect(){
	PyGC_Head * curr;
	obj_set::iterator it;
	PyThreadState* root, *p;
	PyInterpreterState *interp;
	PyFrameObject* frame;
    struct timeval tv1, tv2;
	
	if (accgc_enable == 0){
		return;
	}
	
	ACCGC_LOCK(colored_lock);
	if(alloc_count < ACCGC_THRESHOLD){
		ACCGC_UNLOCK(colored_lock);
		return;
	}
/*
	if(accgc_main_thread != pthread_self()){
		pthread_mutex_unlock(&(root->thread_mutex));
		pthread_mutex_lock(&(root->thread_mutex));
		return;
	}
	
	interp = root->interp;
	for (p = interp->tstate_head; p != NULL; p = p->next) {
		pthread_mutex_lock(&(p->thread_mutex));
	}
	printf("Asquired all locks, running gc\n");
	for (p = interp->tstate_head; p != NULL; p = p->next) {
		pthread_mutex_unlock(&(p->thread_mutex));
	}
*/

	/* START of graph traversal */
	root = PyThreadState_Get();
	if(root->frame)
		frame = root->frame;
	else{
		eprintf("No active frame");
		ACCGC_UNLOCK(colored_lock);
		return;
	}
	perf_start();
		perf_start();
	/* Thread status */
	accgc_move_to_list(root->async_exc, p_accgc_black);
	accgc_move_to_list(root->c_profileobj, p_accgc_black);
	accgc_move_to_list(root->c_traceobj, p_accgc_black);
	accgc_move_to_list(root->curexc_traceback, p_accgc_black);
	accgc_move_to_list(root->curexc_type, p_accgc_black);
	accgc_move_to_list(root->curexc_value, p_accgc_black);
	accgc_move_to_list(root->dict, p_accgc_black);
	accgc_move_to_list(root->exc_traceback, p_accgc_black);
	accgc_move_to_list(root->exc_type, p_accgc_black);
	accgc_move_to_list(root->exc_value, p_accgc_black);
	
	if(root->interp){
		PyInterpreterState_traverse(root->interp, (visitproc)accgc_move_to_list, (void*)p_accgc_black);
	}
#ifdef ACCGC_COUNTERS
	failed = 0;
	move_to_black = 0;
#endif
	accgc_method_cache_traverse(accgc_move_to_list, p_accgc_black);
	perf_inter("thread");
	for(it = accgc_roots.begin(); it != accgc_roots.end(); it++)
		TRAV_OBJ(*it);
	perf_inter("roots");
	
	accgc_collect_types();
	accgc_collect_exceptions();

	accgc_move_to_list((PyObject *)frame, p_accgc_black);

	perf_inter("rest");
	/* START deleting garbage */
	curr = p_accgc_white->gc.gc_next;
	int w_l = 0,  g_l = 0, b_l = 0, d_l = 0;
	while (curr != p_accgc_white){
		PyObject *obj = FROM_GC(curr);
		
		w_l++;
		curr->gc.color = p_accgc_delete;
		curr = curr->gc.gc_next;

		if(in(accgc_roots, obj))
			continue;
		
		PyObject_GC_Del(obj);	// UNDOMMENT : this is THE garbage collection
		dealloc_count++;
	}
	perf_stop("collect");
	
	/*
	 * GC finished, delete unused objects.
	 */
	/*
	while (curr != p_accgc_gray){
		g_l++;
		curr = curr->gc.gc_next;
	}
	curr = p_accgc_black->gc.gc_next;
	while (curr != p_accgc_black){
		b_l++;
		curr = curr->gc.gc_next;
	}
	curr = p_accgc_delete->gc.gc_next;
	while (curr != p_accgc_delete){
		d_l++;
		curr = curr->gc.gc_next;
	}*/

#ifdef ACCGC_COUNTERS
	eprintf("Objects: %i %i failed: %i", w_l, move_to_black, failed);
	eprintf("Moves: %i", move_to_black);
#endif
	gc_list_merge(p_accgc_white, p_accgc_delete); /* delete objects still marked as white */
	accgc_list_cycle();
	
#ifdef ACCGC_COUNT_TYPES
	t_types_map::iterator type = types.begin();
	for(; type != types.end(); type++){
		eprintf(" - %s -> %i", (*type).first, (*type).second);
	}
	types.clear();
#endif
	
	//printf("GC - end\n");
	alloc_count = 0;
	perf_stop("GC");
	ACCGC_UNLOCK(colored_lock);
}

int time_sum = 0;
int alloc_count_all = 0;

PyObject *
_PyObject_GC_Malloc(size_t basicsize){
    struct timeval tv1, tv2;
	
    //gettimeofday(&tv1, NULL);
	PyObject *op;
	PyGC_Head *g;
	if (basicsize > PY_SSIZE_T_MAX - sizeof(PyGC_Head))
		return PyErr_NoMemory();

	alloc_count ++;
	alloc_count_all ++;
	ACCGC_LOCK(colored_lock);
	
	g = (PyGC_Head *)PyObject_MALLOC(sizeof(PyGC_Head) + basicsize);

	if (g == NULL){
		ACCGC_UNLOCK(colored_lock);
		return PyErr_NoMemory();
	}

	op = FROM_GC(g);
	//g->gc.root = 0;
	g->gc.color = p_accgc_white;
	g->gc.gc_next = p_accgc_white;
	g->gc.gc_prev = p_accgc_white->gc.gc_prev;
	g->gc.gc_prev->gc.gc_next = g;
	p_accgc_white->gc.gc_prev = g;
	ACCGC_UNLOCK(colored_lock);
	
    //gettimeofday(&tv2, NULL);
    //time_sum += tv2.tv_usec - tv1.tv_usec + 1000000 * (tv2.tv_sec - tv1.tv_sec);

	return op;
}

PyObject *
_PyObject_GC_New(PyTypeObject *tp)
{
	PyObject *op = _PyObject_GC_Malloc(_PyObject_SIZE(tp));
	if (op != NULL)
		op = PyObject_INIT(op, tp);
	return op;
}

PyVarObject *
_PyObject_GC_NewVar(PyTypeObject *tp, Py_ssize_t nitems)
{
	const size_t size = _PyObject_VAR_SIZE(tp, nitems);
	PyVarObject *op = (PyVarObject *) _PyObject_GC_Malloc(size);
	if (op != NULL)
		op = PyObject_INIT_VAR(op, tp, nitems);
	return op;
}

PyVarObject *
_PyObject_GC_Resize(PyVarObject *op, Py_ssize_t nitems) {
	const size_t basicsize = _PyObject_VAR_SIZE(Py_TYPE(op), nitems);
	PyGC_Head *g = AS_GC(op);
	bool in_root = false;
	
	if (basicsize > PY_SSIZE_T_MAX - sizeof(PyGC_Head))
		return (PyVarObject *)PyErr_NoMemory();

	ACCGC_LOCK(colored_lock);
	g->gc.gc_next->gc.gc_prev = g->gc.gc_prev;
	g->gc.gc_prev->gc.gc_next = g->gc.gc_next; // remove from current gc list, this object will be no longer valid

	if(accgc_roots.count((PyObject*)op)){
		accgc_from_root((PyObject*)op);
		in_root = true;
	}
	g = (PyGC_Head *)PyObject_REALLOC(g,  sizeof(PyGC_Head) + basicsize);
	if (g == NULL){
		ACCGC_UNLOCK(colored_lock);
		return (PyVarObject *)PyErr_NoMemory();
	}

	g->gc.gc_next = p_accgc_white;
	g->gc.gc_prev = p_accgc_white->gc.gc_prev;
	g->gc.gc_prev->gc.gc_next = g;
	p_accgc_white->gc.gc_prev = g; // append to list again
	
	op = (PyVarObject *) FROM_GC(g);
	Py_SIZE(op) = nitems;
	if(in_root)
		accgc_to_root((PyObject*)op);
	ACCGC_UNLOCK(colored_lock);
	return op;
}

void
PyObject_GC_Del(void *op)
{
	if(accgc_roots.count((PyObject*)op))
		accgc_from_root((PyObject*)op);
	PyGC_Head *g = AS_GC(op);
	gc_list_remove(g);
	PyObject_FREE(g);
}

/* for binary compatibility with 2.2 */
#undef _PyObject_GC_Del
void
_PyObject_GC_Del(PyObject *op)
{
    PyObject_GC_Del(op);
}

FILE *log_file;

void accgc_finish(){
	printf("Alloc time %i\n", time_sum);
	printf("Alloc count %i\nDealloc count %i\n", alloc_count_all, dealloc_count);
}

int accgc_init(){
	log_file = stdout;
	eprintf("Init GC");
	accgc_enable = 0;
	p_accgc_delete = &accgc_delete;
	p_accgc_root = &accgc_root;
	//gc_list_init(&accgc_white);
	//gc_list_init(&accgc_gray);
	//gc_list_init(&accgc_black);
	gc_list_init(&(gc_lists[0]));
	gc_list_init(&(gc_lists[1]));
	gc_list_init(&(gc_lists[2]));
	gc_list_init(p_accgc_delete);
	gc_list_init(p_accgc_root);
	white_list = 0;
	accgc_list_cycle();
	accgc_main_thread = pthread_self();
	ACCGC_INITLOCK(colored_lock);
	//pthread_spin_init(&colored_lock, PTHREAD_PROCESS_PRIVATE);
	return 0;
};
