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
#include <algorithm>
#include <set>
#include <hash_set>
#include <list>
using namespace __gnu_cxx;
using namespace std;

/* Get an object's GC head */
//#define AS_GC(o) ((PyGC_Head *)(o)-1)

/* Get the object given the GC head */
//#define FROM_GC(g) ((PyObject *)(((PyGC_Head *)g)+1))

/*** Global GC state ***/

#define LOCK(arg) pthread_spin_lock(&arg);
#define UNLOCK(arg) pthread_spin_unlock(&arg);

struct gc_generation {
	PyGC_Head head;
	int threshold; /* collection threshold */
	int count; /* count of allocations or collections of younger
		      generations */
};


#define NUM_GENERATIONS 3

struct hash_Object{
	size_t operator()(PyObject* const&x)const{
		return ((size_t)x) ;
	}
};
#define in(accgc_roots, obj) accgc_roots.find(obj) != accgc_roots.end()
typedef hash_set<PyObject*, hash_Object > obj_set;
typedef list<PyObject*> obj_list;
//typedef set<PyObject* > obj_set;
typedef stack<PyObject*> obj_stack;
PyGC_Head* p_accgc_white;
PyGC_Head* p_accgc_gray;
PyGC_Head* p_accgc_black;
//PyGC_Head* p_accgc_root;
//PyGC_Head* p_accgc_delete;
int white_list;
PyGC_Head gc_lists[3];
//PyGC_Head accgc_white;
//PyGC_Head accgc_gray;
//PyGC_Head accgc_black;
//PyGC_Head accgc_root;
//PyGC_Head accgc_delete;
obj_set accgc_roots;
obj_list accgc_white;
#define ACCGC_WHITE 1
obj_set accgc_gray;
#define ACCGC_GRAY 2
//obj_stack accgc_gray;
obj_set accgc_black;
#define ACCGC_BLACK 3
int accgc_run = 0;
int accgc_enable = 0;
int accgc_main_thread = 0;

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
		printf(" ");
	printf("Perf time (%s): %d us\n", str, (tv).tv_usec - time_stack.top().tv_usec +
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
		printf(" ");
	printf("Perf time (%s): %d us\n", str, (tv).tv_usec - time_stack.top().tv_usec +
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

SPINLOCK_INIT(colored_lock);
//pthread_spinlock_t colored_lock;
pthread_mutex_t colored_mutex = PTHREAD_MUTEX_INITIALIZER;

int pshared;
#define COL_HEAD(n) (&colored[n])
/* linked lists of container objects */
PyGC_Head colored[3] = {
	{{COL_HEAD(0), COL_HEAD(0), 0}},
	{{COL_HEAD(1), COL_HEAD(1), 0}},
	{{COL_HEAD(2), COL_HEAD(2), 0}},
};


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

/*--------------------------------------------------------------------------
gc_refs values.

Between collections, every gc'ed object has one of two gc_refs values:

GC_UNTRACKED
    The initial state; objects returned by PyObject_GC_Malloc are in this
    state.  The object doesn't live in any generation list, and its
    tp_traverse slot must not be called.

GC_REACHABLE
    The object lives in some generation list, and its tp_traverse is safe to
    call.  An object transitions to GC_REACHABLE when PyObject_GC_Track
    is called.

During a collection, gc_refs can temporarily take on other states:

>= 0
    At the start of a collection, update_refs() copies the true refcount
    to gc_refs, for each object in the generation being collected.
    subtract_refs() then adjusts gc_refs so that it equals the number of
    times an object is referenced directly from outside the generation
    being collected.
    gc_refs remains >= 0 throughout these steps.

GC_TENTATIVELY_UNREACHABLE
    move_unreachable() then moves objects not reachable (whether directly or
    indirectly) from outside the generation into an "unreachable" set.
    Objects that are found to be reachable have gc_refs set to GC_REACHABLE
    again.  Objects that are found to be unreachable have gc_refs set to
    GC_TENTATIVELY_UNREACHABLE.  It's "tentatively" because the pass doing
    this can't be sure until it ends, and GC_TENTATIVELY_UNREACHABLE may
    transition back to GC_REACHABLE.

    Only objects with GC_TENTATIVELY_UNREACHABLE still set are candidates
    for collection.  If it's decided not to collect such an object (e.g.,
    it has a __del__ method), its gc_refs is restored to GC_REACHABLE again.
----------------------------------------------------------------------------
*/
#define GC_UNTRACKED			_PyGC_REFS_UNTRACKED
#define GC_REACHABLE			_PyGC_REFS_REACHABLE
#define GC_TENTATIVELY_UNREACHABLE	_PyGC_REFS_TENTATIVELY_UNREACHABLE

#define IS_TRACKED(o) ((AS_GC(o))->gc.gc_refs != GC_UNTRACKED)
#define IS_REACHABLE(o) ((AS_GC(o))->gc.gc_refs == GC_REACHABLE)
#define IS_TENTATIVELY_UNREACHABLE(o) ( \
	(AS_GC(o))->gc.gc_refs == GC_TENTATIVELY_UNREACHABLE)

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

/* Remove `node` from the gc list it's currently in. */
static void
gc_list_remove(PyGC_Head *node)
{
	
}

/* Move `node` from the gc list it's currently in (which is not explicitly
 * named here) to the end of `list`.  This is semantically the same as
 * gc_list_remove(node) followed by gc_list_append(node, list).
 */
static void
gc_list_move(PyGC_Head *node, PyGC_Head *list)
{
	
}

/* append list `from` onto list `to`; `from` becomes an empty list */
static void
gc_list_merge(PyGC_Head *from, PyGC_Head *to)
{
}

static Py_ssize_t
gc_list_size(PyGC_Head *list)
{
	return 0;
}

/* Append objects in a GC list to a Python list.
 * Return 0 if all OK, < 0 if error (out of memory for list).
 */
static int
append_objects(PyObject *py_list, PyGC_Head *gc_list)
{
	return 0;
}

/*** end of list stuff ***/


/* Set all gc_refs = ob_refcnt.  After this, gc_refs is > 0 for all objects
 * in containers, and is GC_REACHABLE for all tracked gc objects not in
 * containers.
 */
static void
update_refs(PyGC_Head *containers)
{

}

/* A traversal callback for subtract_refs. */
static int
visit_decref(PyObject *op, void *data)
{
	return 0;
}

/* Subtract internal references from gc_refs.  After this, gc_refs is >= 0
 * for all objects in containers, and is GC_REACHABLE for all tracked gc
 * objects not in containers.  The ones with gc_refs > 0 are directly
 * reachable from outside containers, and so can't be collected.
 */
static void
subtract_refs(PyGC_Head *containers)
{
	
}

/* A traversal callback for move_unreachable. */
static int
visit_reachable(PyObject *op, PyGC_Head *reachable)
{

	return 0;
}

/* Move the unreachable objects from young to unreachable.  After this,
 * all objects in young have gc_refs = GC_REACHABLE, and all objects in
 * unreachable have gc_refs = GC_TENTATIVELY_UNREACHABLE.  All tracked
 * gc objects not in young or unreachable still have gc_refs = GC_REACHABLE.
 * All objects in young after this are directly or indirectly reachable
 * from outside the original young; and all objects in unreachable are
 * not.
 */
static void
move_unreachable(PyGC_Head *young, PyGC_Head *unreachable)
{
	
}

/* Return true if object has a finalization method.
 * CAUTION:  An instance of an old-style class has to be checked for a
 *__del__ method, and earlier versions of this used to call PyObject_HasAttr,
 * which in turn could call the class's __getattr__ hook (if any).  That
 * could invoke arbitrary Python code, mutating the object graph in arbitrary
 * ways, and that was the source of some excruciatingly subtle bugs.
 */
static int
has_finalizer(PyObject *op)
{
	if (PyInstance_Check(op)) {
		assert(delstr != NULL);
		return _PyInstance_Lookup(op, delstr) != NULL;
	}
	else if (PyType_HasFeature(op->ob_type, Py_TPFLAGS_HEAPTYPE))
		return op->ob_type->tp_del != NULL;
	else if (PyGen_CheckExact(op))
		return PyGen_NeedsFinalizing((PyGenObject *)op);
	else
		return 0;
}

/* Move the objects in unreachable with __del__ methods into `finalizers`.
 * Objects moved into `finalizers` have gc_refs set to GC_REACHABLE; the
 * objects remaining in unreachable are left at GC_TENTATIVELY_UNREACHABLE.
 */
static void
move_finalizers(PyGC_Head *unreachable, PyGC_Head *finalizers)
{
	
}

/* A traversal callback for move_finalizer_reachable. */
static int
visit_move(PyObject *op, PyGC_Head *tolist)
{
	return 0;
}

/* Move objects that are reachable from finalizers, from the unreachable set
 * into finalizers set.
 */
static void
move_finalizer_reachable(PyGC_Head *finalizers)
{
	
}

/* Clear all weakrefs to unreachable objects, and if such a weakref has a
 * callback, invoke it if necessary.  Note that it's possible for such
 * weakrefs to be outside the unreachable set -- indeed, those are precisely
 * the weakrefs whose callbacks must be invoked.  See gc_weakref.txt for
 * overview & some details.  Some weakrefs with callbacks may be reclaimed
 * directly by this routine; the number reclaimed is the return value.  Other
 * weakrefs with callbacks may be moved into the `old` generation.  Objects
 * moved into `old` have gc_refs set to GC_REACHABLE; the objects remaining in
 * unreachable are left at GC_TENTATIVELY_UNREACHABLE.  When this returns,
 * no object in `unreachable` is weakly referenced anymore.
 */
static int
handle_weakrefs(PyGC_Head *unreachable, PyGC_Head *old)
{
	return 0;
}

static void
debug_instance(char *msg, PyInstanceObject *inst)
{
	char *cname;
	/* simple version of instance_repr */
	PyObject *classname = inst->in_class->cl_name;
	if (classname != NULL && PyString_Check(classname))
		cname = PyString_AsString(classname);
	else
		cname = "?";
	PySys_WriteStderr("gc: %.100s <%.100s instance at %p>\n",
			  msg, cname, inst);
}

static void
debug_cycle(char *msg, PyObject *op)
{

}

/* Handle uncollectable garbage (cycles with finalizers, and stuff reachable
 * only from such cycles).
 * If DEBUG_SAVEALL, all objects in finalizers are appended to the module
 * garbage list (a Python list), else only the objects in finalizers with
 * __del__ methods are appended to garbage.  All objects in finalizers are
 * merged into the old list regardless.
 * Returns 0 if all OK, <0 on error (out of memory to grow the garbage list).
 * The finalizers list is made empty on a successful return.
 */
static int
handle_finalizers(PyGC_Head *finalizers, PyGC_Head *old)
{

	return 0;
}

/* Break reference cycles by clearing the containers involved.	This is
 * tricky business as the lists can be changing and we don't know which
 * objects may be freed.  It is possible I screwed something up here.
 */
static void
delete_garbage(PyGC_Head *collectable, PyGC_Head *old)
{
	
}

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

/* This is the main function.  Read this to understand how the
 * collection process works. */
static Py_ssize_t
collect(int generation)
{
	return 0;
}

static Py_ssize_t
collect_generations(void)
{
	return 0;
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
gc_collect(PyObject *self, PyObject *args, PyObject *kws)
{
	static char *keywords[] = {"generation", NULL};
	int genarg = NUM_GENERATIONS - 1;
	Py_ssize_t n;

	if (!PyArg_ParseTupleAndKeywords(args, kws, "|i", keywords, &genarg))
		return NULL;

	else if (genarg < 0 || genarg >= NUM_GENERATIONS) {
		PyErr_SetString(PyExc_ValueError, "invalid generation");
		return NULL;
	}

	if (collecting)
		n = 0; /* already collecting, don't do anything */
	else {
		collecting = 1;
		n = collect(genarg);
		collecting = 0;
	}

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
	return Py_None;
}

PyDoc_STRVAR(gc_get_thresh__doc__,
"get_threshold() -> (threshold0, threshold1, threshold2)\n"
"\n"
"Return the current collection thresholds\n");

static PyObject *
gc_get_thresh(PyObject *self, PyObject *noargs)
{	
	return Py_None;
}

PyDoc_STRVAR(gc_get_count__doc__,
"get_count() -> (count0, count1, count2)\n"
"\n"
"Return the current collection counts\n");

static PyObject *
gc_get_count(PyObject *self, PyObject *noargs)
{
	return Py_None;
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
	return 1; /* no error */
}

PyDoc_STRVAR(gc_get_referrers__doc__,
"get_referrers(*objs) -> list\n\
Return the list of objects that directly refer to any of objs.");

static PyObject *
gc_get_referrers(PyObject *self, PyObject *args)
{
	return Py_None;
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
	return Py_None;
}

PyDoc_STRVAR(gc_get_objects__doc__,
"get_objects() -> [...]\n"
"\n"
"Return a list of objects tracked by the collector (excluding the list\n"
"returned).\n");

static PyObject *
gc_get_objects(PyObject *self, PyObject *noargs)
{
	return Py_None;
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
	Py_ssize_t n;
	if (collecting)
		n = 0; /* already collecting, don't do anything */
	else {
		collecting = 1;
		n = collect(NUM_GENERATIONS - 1);
		collecting = 0;
	}

	return n;
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
int move_hits = 0, moves = 0;
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

int accgc_move_objs(PyObject *obj, void * list){
	traverseproc traverse;
	obj_list::iterator *it;
	move_hits++;
	if(!obj)
		return 0;
	
	if(in(accgc_black, obj))
		return 0;
	
	if(in(accgc_gray, obj))
		return 0;
	
	if(obj->it != (void*)0xcbcbcbcb && obj->it != NULL){
		eprintf("checking %p", obj);
		it = (obj_list::iterator*)(obj->it);
		accgc_white.erase(*it);
		obj->it = NULL;
		traverse = obj->ob_type->tp_traverse;
		if(traverse){
			accgc_gray.insert(obj);
		}else{
			accgc_black.insert(obj);
		#ifdef ACCGC_COUNTERS
			move_to_black++;
		#endif
		}
	}
	
	moves++;
	return 0;
}

int accgc_collect_loop(){
	traverseproc traverse;
	int tr_res;
	PyObject *obj;
	while(!accgc_gray.empty()){
		obj = *(accgc_gray.begin());
		
		traverse = obj->ob_type->tp_traverse;
		tr_res = traverse(obj,
				(visitproc)accgc_move_objs,
				NULL);
		accgc_gray.erase(obj);
		accgc_black.insert(obj);
#ifdef ACCGC_COUNTERS
		move_to_black++;
#endif
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

/*
 * Moves objct to root objects list. These objects are start points for GC.
 */
void accgc_to_root(PyObject* obj){
	accgc_roots.insert( obj);
}

/*
 * Remove object from root objects list. In most cases, this object is no longer used.
 */
void accgc_from_root(PyObject* obj){
	//accgc_white.insert(obj);
	accgc_roots.erase(obj);
}

#define exp_point(exp) (PyExc_ ## exp)
#define TRAV_OBJ(obj) accgc_move_objs((PyObject *)(obj), NULL);
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
	//TRAV_OBJ((PyObject *)&PyType_Type);
	TRAV_OBJ((PyObject *)&_PyWeakref_RefType);
	TRAV_OBJ((PyObject *)&_PyWeakref_CallableProxyType);
	TRAV_OBJ((PyObject *)&_PyWeakref_ProxyType);
	TRAV_OBJ((PyObject *)&PyBool_Type);
	TRAV_OBJ((PyObject *)&PyString_Type);
	TRAV_OBJ((PyObject *)&PyByteArray_Type);
	TRAV_OBJ((PyObject *)&PyList_Type);
	TRAV_OBJ((PyObject *)&PyNone_Type);
	TRAV_OBJ((PyObject *)&PyNotImplemented_Type);
	TRAV_OBJ((PyObject *)&PyTraceBack_Type);
	TRAV_OBJ((PyObject *)&PySuper_Type);
	TRAV_OBJ((PyObject *)&PyBaseObject_Type);
	TRAV_OBJ((PyObject *)&PyRange_Type);
	TRAV_OBJ((PyObject *)&PyDict_Type);
	TRAV_OBJ((PyObject *)&PySet_Type);
	TRAV_OBJ((PyObject *)&PyUnicode_Type);
	TRAV_OBJ((PyObject *)&PySlice_Type);
	TRAV_OBJ((PyObject *)&PyStaticMethod_Type);
	#ifndef WITHOUT_COMPLEX
	TRAV_OBJ((PyObject *)&PyComplex_Type);
	#endif
	TRAV_OBJ((PyObject *)&PyFloat_Type);
	TRAV_OBJ((PyObject *)&PyBuffer_Type);
	TRAV_OBJ((PyObject *)&PyLong_Type);
	TRAV_OBJ((PyObject *)&PyInt_Type);
	TRAV_OBJ((PyObject *)&PyFrozenSet_Type);
	TRAV_OBJ((PyObject *)&PyProperty_Type);
	TRAV_OBJ((PyObject *)&PyTuple_Type);
	TRAV_OBJ((PyObject *)&PyEnum_Type);
	TRAV_OBJ((PyObject *)&PyReversed_Type);
	TRAV_OBJ((PyObject *)&PyCode_Type);
	TRAV_OBJ((PyObject *)&PyFrame_Type);
	TRAV_OBJ((PyObject *)&PyCFunction_Type);
	TRAV_OBJ((PyObject *)&PyMethod_Type);
	TRAV_OBJ((PyObject *)&PyFunction_Type);
	TRAV_OBJ((PyObject *)&PyClass_Type);
	TRAV_OBJ((PyObject *)&PyDictProxy_Type);
	TRAV_OBJ((PyObject *)&PyGen_Type);
	TRAV_OBJ((PyObject *)&PyGetSetDescr_Type);
	TRAV_OBJ((PyObject *)&PyWrapperDescr_Type);
	TRAV_OBJ((PyObject *)&PyInstance_Type);
	TRAV_OBJ((PyObject *)&PyEllipsis_Type);
	TRAV_OBJ((PyObject *)&PyMemberDescr_Type);
}

void accgc_collect(){
	return;
	//printf("white size %i\n", accgc_white.size());
	//accgc_white.clear();
	//return;
	obj_set::iterator it;
	PyThreadState* root, *p;
	PyInterpreterState *interp;
	PyFrameObject* frame;
	PyObject *obj;
	int w_l = 0,  g_l = 0, b_l = 0, d_l = 0;
    
	root = PyThreadState_Get();
	if (accgc_enable == 0)
		return;

	if(alloc_count < 10000)
		return;
    perf_start();
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
	
	if(root->frame)
		frame = root->frame;
	else{
		eprintf("No active frame");
		return;
	}
#ifdef ACCGC_COUNTERS
	failed = 0;
	move_to_black = 0;
	w_l = 0;
#endif
	perf_start();
	eprintf(" -- Roots size %i", accgc_roots.size());
	for(it = accgc_roots.begin(); it != accgc_roots.end(); it++)
		TRAV_OBJ(*it);
	perf_inter("ROOTS");
	/* Thread status */
	TRAV_OBJ(root->async_exc);
	TRAV_OBJ(root->c_profileobj);
	TRAV_OBJ(root->c_traceobj);
	TRAV_OBJ(root->curexc_traceback);
	TRAV_OBJ(root->curexc_type);
	TRAV_OBJ(root->curexc_value);
	TRAV_OBJ(root->dict);
	TRAV_OBJ(root->exc_traceback);
	TRAV_OBJ(root->exc_type);
	TRAV_OBJ(root->exc_value);

	perf_inter("Thread");
	accgc_collect_types();
	accgc_collect_exceptions();
	accgc_method_cache_traverse(accgc_move_objs, NULL);

	perf_inter("types, exceptions and method cache");
	if(root->interp)
		PyInterpreterState_traverse(root->interp, (visitproc)accgc_move_objs, NULL);

	TRAV_OBJ((PyObject *)frame);
	accgc_collect_loop();
	perf_inter("the rest");
	
	obj_list::iterator itl;
	obj_list::iterator end = accgc_white.end();
	for(itl = accgc_white.begin(); itl != end; itl++){
		//obj = *(itl);
		//obj->it = NULL;
		PyObject_GC_Del(*(itl));
	}
	accgc_white = obj_list();
	perf_stop("delete");
#ifdef ACCGC_COUNTERS
	eprintf("Objects: %i %i failed: %i", w_l, move_to_black, failed);
#endif
	
#ifdef ACCGC_COUNT_TYPES
	t_types_map::iterator type = types.begin();
	for(; type != types.end(); type++){
		eprintf(" - %s -> %i", (*type).first, (*type).second);
	}
	types.clear();
#endif
	//printf("%i %i\n", move_hits, moves);
	perf_stop();
}

PyObject *
_PyObject_GC_Malloc(size_t basicsize)
{
	PyObject *op;
	if (basicsize > PY_SSIZE_T_MAX)
		return PyErr_NoMemory();

	alloc_count ++;
	LOCK(colored_lock);
	
	op = (PyObject*)PyObject_MALLOC(basicsize);

	if (op == NULL){
		UNLOCK(colored_lock);
		return PyErr_NoMemory();
	}
	op->it = new obj_list::iterator(accgc_white.insert(accgc_white.begin(), op));
	UNLOCK(colored_lock);
	eprintf("Allocated %p\n", op);
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
_PyObject_GC_Resize(PyVarObject *op, Py_ssize_t nitems)
{
	PyVarObject *obj;
	const size_t basicsize = _PyObject_VAR_SIZE(Py_TYPE(op), nitems);
	if (basicsize > PY_SSIZE_T_MAX)
		return (PyVarObject *)PyErr_NoMemory();

	accgc_roots.erase((PyObject*)op);
	if(op->it)
		accgc_white.erase(*((obj_list::iterator*)(op->it)));
	accgc_gray.erase((PyObject*)op);

	eprintf("Resized %p", op);

	obj = (PyVarObject *)PyObject_REALLOC(op,  basicsize);
	eprintf("\t-> %p", obj);
	if (obj == NULL)
		return (PyVarObject *)PyErr_NoMemory();
	
	obj->it = new obj_list::iterator(accgc_white.insert(accgc_white.begin(),(PyObject*)obj));
	Py_SIZE(obj) = nitems;
	return obj;
}

void
PyObject_GC_Del(void *op)
{
	if(accgc_roots.count((PyObject*)op))
		accgc_from_root((PyObject*)op);
	PyObject_FREE(op);
}

/* for binary compatibility with 2.2 */
#undef _PyObject_GC_Del
void
_PyObject_GC_Del(PyObject *op)
{
    PyObject_GC_Del(op);
}

FILE *log_file;

int accgc_init(){
	log_file = stdout;
	eprintf("Init GC");
	accgc_enable = 0;
	//p_accgc_root = &accgc_root;
	//gc_list_init(&accgc_white);
	//gc_list_init(&accgc_gray);
	//gc_list_init(&accgc_black);
	gc_list_init(&(gc_lists[0]));
	gc_list_init(&(gc_lists[1]));
	gc_list_init(&(gc_lists[2]));
	//gc_list_init(p_accgc_root);
	white_list = 0;
	accgc_list_cycle();
	accgc_main_thread = pthread_self();
	pthread_spin_init(&colored_lock, pshared);
	return 0;
};
