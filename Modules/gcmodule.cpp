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

//#include <set>
#include <hash_set>
using namespace __gnu_cxx;
using namespace std;

/* Get an object's GC head */
#define AS_GC(o) ((PyGC_Head *)(o)-1)

/* Get the object given the GC head */
#define FROM_GC(g) ((PyObject *)(((PyGC_Head *)g)+1))

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

/* linked lists of container objects */
/*
static struct gc_generation generations[NUM_GENERATIONS] = {
	{{{GEN_HEAD(0), GEN_HEAD(0), 0, &accgc_white}},	700,		0},
	{{{GEN_HEAD(1), GEN_HEAD(1), 0, &accgc_white}},	10,		0},
	{{{GEN_HEAD(2), GEN_HEAD(2), 0, &accgc_white}},	10,		0},
};*/

struct hash_Object{
	size_t operator()(PyObject* const&x)const{
		return (size_t)x;
	}
};
#define in(accgc_roots, obj) accgc_roots.find(obj) != accgc_roots.end()
typedef hash_set<PyObject*, hash_Object > obj_set;
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
obj_set accgc_white;
obj_set accgc_gray;
//obj_stack accgc_gray;
obj_set accgc_black;
int accgc_run = 0;
int accgc_enable = 0;
int accgc_main_thread = 0;

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


/* Set all gc_refs = ob_refcnt.  After this, gc_refs is > 0 for all objects
 * in containers, and is GC_REACHABLE for all tracked gc objects not in
 * containers.
 */
static void
update_refs(PyGC_Head *containers)
{
	PyGC_Head *gc = containers->gc.gc_next;
	for (; gc != containers; gc = gc->gc.gc_next) {
		assert(gc->gc.gc_refs == GC_REACHABLE);
		gc->gc.gc_refs = Py_REFCNT(FROM_GC(gc));
		/* Python's cyclic gc should never see an incoming refcount
		 * of 0:  if something decref'ed to 0, it should have been
		 * deallocated immediately at that time.
		 * Possible cause (if the assert triggers):  a tp_dealloc
		 * routine left a gc-aware object tracked during its teardown
		 * phase, and did something-- or allowed something to happen --
		 * that called back into Python.  gc can trigger then, and may
		 * see the still-tracked dying object.  Before this assert
		 * was added, such mistakes went on to allow gc to try to
		 * delete the object again.  In a debug build, that caused
		 * a mysterious segfault, when _Py_ForgetReference tried
		 * to remove the object from the doubly-linked list of all
		 * objects a second time.  In a release build, an actual
		 * double deallocation occurred, which leads to corruption
		 * of the allocator's internal bookkeeping pointers.  That's
		 * so serious that maybe this should be a release-build
		 * check instead of an assert?
		 */
		assert(gc->gc.gc_refs != 0);
	}
}

/* A traversal callback for subtract_refs. */
static int
visit_decref(PyObject *op, void *data)
{
        assert(op != NULL);
	if (PyObject_IS_GC(op)) {
		PyGC_Head *gc = AS_GC(op);
		/* We're only interested in gc_refs for objects in the
		 * generation being collected, which can be recognized
		 * because only they have positive gc_refs.
		 */
		assert(gc->gc.gc_refs != 0); /* else refcount was too small */
		if (gc->gc.gc_refs > 0)
			gc->gc.gc_refs--;
	}
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
	traverseproc traverse;
	PyGC_Head *gc = containers->gc.gc_next;
	for (; gc != containers; gc=gc->gc.gc_next) {
		traverse = Py_TYPE(FROM_GC(gc))->tp_traverse;
		(void) traverse(FROM_GC(gc),
			       (visitproc)visit_decref,
			       NULL);
	}
}

/* A traversal callback for move_unreachable. */
static int
visit_reachable(PyObject *op, PyGC_Head *reachable)
{
	if (PyObject_IS_GC(op)) {
		PyGC_Head *gc = AS_GC(op);
		const Py_ssize_t gc_refs = gc->gc.gc_refs;

		if (gc_refs == 0) {
			/* This is in move_unreachable's 'young' list, but
			 * the traversal hasn't yet gotten to it.  All
			 * we need to do is tell move_unreachable that it's
			 * reachable.
			 */
			gc->gc.gc_refs = 1;
		}
		else if (gc_refs == GC_TENTATIVELY_UNREACHABLE) {
			/* This had gc_refs = 0 when move_unreachable got
			 * to it, but turns out it's reachable after all.
			 * Move it back to move_unreachable's 'young' list,
			 * and move_unreachable will eventually get to it
			 * again.
			 */
			gc_list_move(gc, reachable);
			gc->gc.gc_refs = 1;
		}
		/* Else there's nothing to do.
		 * If gc_refs > 0, it must be in move_unreachable's 'young'
		 * list, and move_unreachable will eventually get to it.
		 * If gc_refs == GC_REACHABLE, it's either in some other
		 * generation so we don't care about it, or move_unreachable
		 * already dealt with it.
		 * If gc_refs == GC_UNTRACKED, it must be ignored.
		 */
		 else {
		 	assert(gc_refs > 0
		 	       || gc_refs == GC_REACHABLE
		 	       || gc_refs == GC_UNTRACKED);
		 }
	}
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
	PyGC_Head *gc = young->gc.gc_next;

	/* Invariants:  all objects "to the left" of us in young have gc_refs
	 * = GC_REACHABLE, and are indeed reachable (directly or indirectly)
	 * from outside the young list as it was at entry.  All other objects
	 * from the original young "to the left" of us are in unreachable now,
	 * and have gc_refs = GC_TENTATIVELY_UNREACHABLE.  All objects to the
	 * left of us in 'young' now have been scanned, and no objects here
	 * or to the right have been scanned yet.
	 */

	while (gc != young) {
		PyGC_Head *next;

		if (gc->gc.gc_refs) {
                        /* gc is definitely reachable from outside the
                         * original 'young'.  Mark it as such, and traverse
                         * its pointers to find any other objects that may
                         * be directly reachable from it.  Note that the
                         * call to tp_traverse may append objects to young,
                         * so we have to wait until it returns to determine
                         * the next object to visit.
                         */
                        PyObject *op = FROM_GC(gc);
                        traverseproc traverse = Py_TYPE(op)->tp_traverse;

                        assert(gc->gc.gc_refs > 0);
                        gc->gc.gc_refs = GC_REACHABLE;
                        
                        (void) traverse(op,
                                        (visitproc)visit_reachable,
                                        (void *)young);
                        next = gc->gc.gc_next;
		}
		else {
			/* This *may* be unreachable.  To make progress,
			 * assume it is.  gc isn't directly reachable from
			 * any object we've already traversed, but may be
			 * reachable from an object we haven't gotten to yet.
			 * visit_reachable will eventually move gc back into
			 * young if that's so, and we'll see it again.
			 */
			next = gc->gc.gc_next;
			gc_list_move(gc, unreachable);
			gc->gc.gc_refs = GC_TENTATIVELY_UNREACHABLE;
		}
		gc = next;
	}
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
	PyGC_Head *gc;
	PyGC_Head *next;

	/* March over unreachable.  Move objects with finalizers into
	 * `finalizers`.
	 */
	for (gc = unreachable->gc.gc_next; gc != unreachable; gc = next) {
		PyObject *op = FROM_GC(gc);

		assert(IS_TENTATIVELY_UNREACHABLE(op));
		next = gc->gc.gc_next;

		if (has_finalizer(op)) {
			gc_list_move(gc, finalizers);
			gc->gc.gc_refs = GC_REACHABLE;
		}
	}
}

/* A traversal callback for move_finalizer_reachable. */
static int
visit_move(PyObject *op, PyGC_Head *tolist)
{
	if (PyObject_IS_GC(op)) {
		if (IS_TENTATIVELY_UNREACHABLE(op)) {
			PyGC_Head *gc = AS_GC(op);
			gc_list_move(gc, tolist);
			gc->gc.gc_refs = GC_REACHABLE;
		}
	}
	return 0;
}

/* Move objects that are reachable from finalizers, from the unreachable set
 * into finalizers set.
 */
static void
move_finalizer_reachable(PyGC_Head *finalizers)
{
	traverseproc traverse;
	PyGC_Head *gc = finalizers->gc.gc_next;
	for (; gc != finalizers; gc = gc->gc.gc_next) {
		/* Note that the finalizers list may grow during this. */
		traverse = Py_TYPE(FROM_GC(gc))->tp_traverse;
		(void) traverse(FROM_GC(gc),
				(visitproc)visit_move,
				(void *)finalizers);
	}
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
	PyGC_Head *gc;
	PyObject *op;		/* generally FROM_GC(gc) */
	PyWeakReference *wr;	/* generally a cast of op */
	PyGC_Head wrcb_to_call;	/* weakrefs with callbacks to call */
	PyGC_Head *next;
	int num_freed = 0;

	gc_list_init(&wrcb_to_call);

	/* Clear all weakrefs to the objects in unreachable.  If such a weakref
	 * also has a callback, move it into `wrcb_to_call` if the callback
	 * needs to be invoked.  Note that we cannot invoke any callbacks until
	 * all weakrefs to unreachable objects are cleared, lest the callback
	 * resurrect an unreachable object via a still-active weakref.  We
	 * make another pass over wrcb_to_call, invoking callbacks, after this
	 * pass completes.
	 */
	for (gc = unreachable->gc.gc_next; gc != unreachable; gc = next) {
		PyWeakReference **wrlist;

		op = FROM_GC(gc);
		assert(IS_TENTATIVELY_UNREACHABLE(op));
		next = gc->gc.gc_next;

		if (! PyType_SUPPORTS_WEAKREFS(Py_TYPE(op)))
			continue;

		/* It supports weakrefs.  Does it have any? */
		wrlist = (PyWeakReference **)
			     		PyObject_GET_WEAKREFS_LISTPTR(op);

		/* `op` may have some weakrefs.  March over the list, clear
		 * all the weakrefs, and move the weakrefs with callbacks
		 * that must be called into wrcb_to_call.
		 */
		for (wr = *wrlist; wr != NULL; wr = *wrlist) {
			PyGC_Head *wrasgc;	/* AS_GC(wr) */

			/* _PyWeakref_ClearRef clears the weakref but leaves
			 * the callback pointer intact.  Obscure:  it also
			 * changes *wrlist.
			 */
			assert(wr->wr_object == op);
			_PyWeakref_ClearRef(wr);
			assert(wr->wr_object == Py_None);
			if (wr->wr_callback == NULL)
				continue;	/* no callback */

	/* Headache time.  `op` is going away, and is weakly referenced by
	 * `wr`, which has a callback.  Should the callback be invoked?  If wr
	 * is also trash, no:
	 *
	 * 1. There's no need to call it.  The object and the weakref are
	 *    both going away, so it's legitimate to pretend the weakref is
	 *    going away first.  The user has to ensure a weakref outlives its
	 *    referent if they want a guarantee that the wr callback will get
	 *    invoked.
	 *
	 * 2. It may be catastrophic to call it.  If the callback is also in
	 *    cyclic trash (CT), then although the CT is unreachable from
	 *    outside the current generation, CT may be reachable from the
	 *    callback.  Then the callback could resurrect insane objects.
	 *
	 * Since the callback is never needed and may be unsafe in this case,
	 * wr is simply left in the unreachable set.  Note that because we
	 * already called _PyWeakref_ClearRef(wr), its callback will never
	 * trigger.
	 *
	 * OTOH, if wr isn't part of CT, we should invoke the callback:  the
	 * weakref outlived the trash.  Note that since wr isn't CT in this
	 * case, its callback can't be CT either -- wr acted as an external
	 * root to this generation, and therefore its callback did too.  So
	 * nothing in CT is reachable from the callback either, so it's hard
	 * to imagine how calling it later could create a problem for us.  wr
	 * is moved to wrcb_to_call in this case.
	 */
	 		if (IS_TENTATIVELY_UNREACHABLE(wr))
	 			continue;
			assert(IS_REACHABLE(wr));

			/* Create a new reference so that wr can't go away
			 * before we can process it again.
			 */
			Py_INCREF(wr);

			/* Move wr to wrcb_to_call, for the next pass. */
			wrasgc = AS_GC(wr);
			assert(wrasgc != next); /* wrasgc is reachable, but
			                           next isn't, so they can't
			                           be the same */
			gc_list_move(wrasgc, &wrcb_to_call);
		}
	}

	/* Invoke the callbacks we decided to honor.  It's safe to invoke them
	 * because they can't reference unreachable objects.
	 */
	while (! gc_list_is_empty(&wrcb_to_call)) {
		PyObject *temp;
		PyObject *callback;

		gc = wrcb_to_call.gc.gc_next;
		op = FROM_GC(gc);
		assert(IS_REACHABLE(op));
		assert(PyWeakref_Check(op));
		wr = (PyWeakReference *)op;
		callback = wr->wr_callback;
		assert(callback != NULL);

		/* copy-paste of weakrefobject.c's handle_callback() */
		temp = PyObject_CallFunctionObjArgs(callback, wr, NULL);
		if (temp == NULL)
			PyErr_WriteUnraisable(callback);
		else
			Py_DECREF(temp);

		/* Give up the reference we created in the first pass.  When
		 * op's refcount hits 0 (which it may or may not do right now),
		 * op's tp_dealloc will decref op->wr_callback too.  Note
		 * that the refcount probably will hit 0 now, and because this
		 * weakref was reachable to begin with, gc didn't already
		 * add it to its count of freed objects.  Example:  a reachable
		 * weak value dict maps some key to this reachable weakref.
		 * The callback removes this key->weakref mapping from the
		 * dict, leaving no other references to the weakref (excepting
		 * ours).
		 */
		Py_DECREF(op);
		if (wrcb_to_call.gc.gc_next == gc) {
			/* object is still alive -- move it */
			gc_list_move(gc, old);
		}
		else
			++num_freed;
	}

	return num_freed;
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
	if ((debug & DEBUG_INSTANCES) && PyInstance_Check(op)) {
		debug_instance(msg, (PyInstanceObject *)op);
	}
	else if (debug & DEBUG_OBJECTS) {
		PySys_WriteStderr("gc: %.100s <%.100s %p>\n",
				  msg, Py_TYPE(op)->tp_name, op);
	}
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
	PyGC_Head *gc = finalizers->gc.gc_next;

	if (garbage == NULL) {
		garbage = PyList_New(0);
		if (garbage == NULL)
			Py_FatalError("gc couldn't create gc.garbage list");
	}
	for (; gc != finalizers; gc = gc->gc.gc_next) {
		PyObject *op = FROM_GC(gc);

		if ((debug & DEBUG_SAVEALL) || has_finalizer(op)) {
			if (PyList_Append(garbage, op) < 0)
				return -1;
		}
	}

	gc_list_merge(finalizers, old);
	return 0;
}

/* Break reference cycles by clearing the containers involved.	This is
 * tricky business as the lists can be changing and we don't know which
 * objects may be freed.  It is possible I screwed something up here.
 */
static void
delete_garbage(PyGC_Head *collectable, PyGC_Head *old)
{
	inquiry clear;

	while (!gc_list_is_empty(collectable)) {
		PyGC_Head *gc = collectable->gc.gc_next;
		PyObject *op = FROM_GC(gc);

		assert(IS_TENTATIVELY_UNREACHABLE(op));
		if (debug & DEBUG_SAVEALL) {
			PyList_Append(garbage, op);
		}
		else {
			if ((clear = Py_TYPE(op)->tp_clear) != NULL) {
				Py_INCREF(op);
				clear(op);
				Py_DECREF(op);
			}
		}
		if (collectable->gc.gc_next == gc) {
			/* object is still alive, move it, it may die later */
			gc_list_move(gc, old);
			gc->gc.gc_refs = GC_REACHABLE;
		}
	}
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
	
	if(in(accgc_black, obj))
		return 0;
	
	if(in(accgc_gray, obj))
		return 0;
	
	traverse = obj->ob_type->tp_traverse;
	if(traverse){
		accgc_white.erase(obj);
		accgc_gray.insert(obj);
	}else{
		accgc_white.erase(obj);
		accgc_black.insert(obj);
	}
	return 0;
}

int accgc_collect(){
	traverseproc traverse;
	int tr_res;
	while(!accgc_gray.empty()){
		PyObject *obj = *(accgc_gray.end());
		traverse = obj->ob_type->tp_traverse;
		tr_res = traverse(obj,
				(visitproc)accgc_move_objs,
				NULL);
		accgc_gray.erase(obj);
		accgc_black.insert(obj);
	}
	return 0;
}
/*
int accgc_move_to_list(PyObject *obj, void * list){
	traverseproc traverse;
	int tr_res;
	
	if (!obj)
		return 0;
	
	if(in(accgc_roots, obj))
		return 0;

#ifdef ACCGC_COUNTERS
	if(in(accgc_black, obj)){
		failed++;
		eprintf("Failed object %p of type %s", obj, tp_name);
		return 0;
	}
#endif
	
	if(in(accgc_white, obj)){
		traverse = obj->ob_type->tp_traverse;
		if (traverse!=0){
#ifdef ACCGC_COUNT_TYPES
			const char* tp_name = obj->ob_type->tp_name;
			if(types.count(tp_name) == 0)
				types[tp_name] = 1;
			else
				types[tp_name] = types[tp_name]+1;
#endif
			accgc_white.erase(obj);
			accgc_gray.insert(obj);
			tr_res = traverse(obj,
					(visitproc)accgc_move_to_list,
					p_accgc_black);
			accgc_gray.erase(obj);
		}else{
			accgc_white.erase(obj);
		}
#ifdef ACCGC_COUNTERS
		move_to_black++;
#endif
		accgc_black.insert(obj);
	}
	return 0;
}
*/
void accgc_list_cycle(){
	white_list += 2;
	white_list %= 3;
	p_accgc_white = &(gc_lists[white_list]);
	p_accgc_gray = &(gc_lists[(white_list+1)%3]);
	p_accgc_black = &(gc_lists[(white_list+2)%3]);
}

void traverse_obj(PyObject* obj, visitproc proc){
	accgc_move_objs(obj, NULL);
}

/*
 * Moves objct to root objects list. These objects are start points for GC.
 */
void accgc_to_root(PyObject* obj){
	accgc_roots.insert(obj);
}

/*
 * Remove object from root objects list. In most cases, this object is no longer used.
 */
void accgc_from_root(PyObject* obj){
	accgc_roots.erase(obj);
}

#define exp_point(exp) (PyExc_ ## exp)
#define TRAV_OBJ(obj) traverse_obj((PyObject *)(obj), NULL);
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
	//PyGC_Head * curr;
	obj_set::iterator it;
	PyThreadState* root, *p;
	PyInterpreterState *interp;
	PyFrameObject* frame;
	
	root = PyThreadState_Get();
	if (accgc_enable == 0){
		return;
	}

	if(alloc_count < 10000){
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
	
	if(root->frame)
		frame = root->frame;
	else{
		eprintf("No active frame");
		return;
	}
#ifdef ACCGC_COUNTERS
	failed = 0;
	move_to_black = 0;
#endif
	accgc_method_cache_traverse(accgc_move_to_list, p_accgc_black);
	
	for(it = accgc_roots.begin(); it != accgc_roots.end(); it++)
		TRAV_OBJ(*it);
	
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
	
	accgc_collect_types();
	accgc_collect_exceptions();

	if(root->interp){
		PyInterpreterState_traverse(root->interp, (visitproc)accgc_move_objs, (void*)p_accgc_black);
	}
	TRAV_OBJ((PyObject *)frame);
	accgc_collect();
	//accgc_move_to_list((PyObject *)frame, p_accgc_black);
	
	int w_l = 0,  g_l = 0, b_l = 0, d_l = 0;
	for(it = accgc_white.begin(); it != accgc_white.end(); it++){
		PyObject *obj = *it;

		if(in(accgc_roots, obj))
			continue;
		
		PyObject_GC_Del(obj);
	}
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
	
	eprintf("GC - end");
}

PyObject *
_PyObject_GC_Malloc(size_t basicsize)
{
	PyObject *op;
	PyGC_Head *g;
	if (basicsize > PY_SSIZE_T_MAX - sizeof(PyGC_Head))
		return PyErr_NoMemory();

	alloc_count ++;
	LOCK(colored_lock);
	
	g = (PyGC_Head *)PyObject_MALLOC(
                sizeof(PyGC_Head) + basicsize);

	if (g == NULL){
		UNLOCK(colored_lock);
		return PyErr_NoMemory();
	}

	op = FROM_GC(g);
	g->gc.root = 0;
	g->gc.color = p_accgc_white;
	g->gc.gc_next = p_accgc_white;
	g->gc.gc_prev = p_accgc_white->gc.gc_prev;
	g->gc.gc_prev->gc.gc_next = g;
	p_accgc_white->gc.gc_prev = g;
	UNLOCK(colored_lock);
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
	const size_t basicsize = _PyObject_VAR_SIZE(Py_TYPE(op), nitems);
	PyGC_Head *g = AS_GC(op);
	if (basicsize > PY_SSIZE_T_MAX - sizeof(PyGC_Head))
		return (PyVarObject *)PyErr_NoMemory();
	
	g->gc.gc_next->gc.gc_prev = g->gc.gc_prev;
	g->gc.gc_prev->gc.gc_next = g->gc.gc_next; // remove from current gc list, this object will be no longer valid
	g = (PyGC_Head *)PyObject_REALLOC(g,  sizeof(PyGC_Head) + basicsize);
	if (g == NULL)
		return (PyVarObject *)PyErr_NoMemory();

	g->gc.gc_next = p_accgc_white;
	g->gc.gc_prev = p_accgc_white->gc.gc_prev;
	g->gc.gc_prev->gc.gc_next = g;
	p_accgc_white->gc.gc_prev = g; // append to list again
	
	op = (PyVarObject *) FROM_GC(g);
	Py_SIZE(op) = nitems;
	return op;
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
