/**
 * @author Daniel Grund
 * @date 04.01.2005
 */

#include <stdlib.h>

#include "obst.h"
#include "set.h"
#include "pset.h"
#include "bitset.h"
#include "debug.h"
#include "irouts.h"
#include "irdom.h"

#include "bechordal.h"
#include "belive_t.h"
#include "bera_t.h"
#include "phiclass_t.h"
#include "bephicoal_t.h"

#define DEBUG_LVL SET_LEVEL_3
#define MAX_COLORS 16

#define INITIAL_SLOTS_PINNED_GLOBAL 256
#define INITIAL_SLOTS_FREE_NODES    128
#define INITIAL_SLOTS_CHANGED_NODES 32

/* some things for readable code */
#define CHANGE_SAVE NULL
#define CHANGE_IMPOSSIBLE (ir_node *)1
#define CHANGE_NYI (ir_node *)2
#define is_conflicting_node(n) (((int)n) > 2)

/**
 * Models conflicts between nodes. These may be life range conflicts or
 * pinning conflicts which may occur while changing colors
 */
typedef struct _conflict_t {
	ir_node *n1, *n2;
} conflict_t;

/**
 * If an irn is changed, the changes first get stored in a node_stat_t,
 * to allow undo of changes in case of conflicts.
 */
typedef struct _node_stat_t {
	ir_node *irn;
	int color;
	int undo_color;
	char status;		/**< Bit 0: pinned, Bit 1: removed */
} node_stat_t;

#define _set_pinned(nodestat)    nodestat->status |= 1
#define _set_removed(nodestat)   nodestat->status |= 2
#define _clear_pinned(nodestat)  nodestat->status &= 255 ^ 1
#define _clear_removed(nodestat) nodestat->status &= 255 ^ 2
#define _is_pinned(nodestat)     (nodestat->status & 1)
#define _is_removed(nodestat)    (nodestat->status & 2)

/**
 * Central data structure. Contains infos needed during coalescing of the
 * corresponding phi class.
 */
typedef struct _phi_unit_t {
	unsigned char phi_count;			/**< the number of phi nodes in this unit */
	/* 1 phi */
	unsigned char node_count;			/**< size of the nodes-array */
	unsigned char conflict_count;		/**< size of the conflicts-array */
	unsigned char conflict_count_org;	/**< initial size of the conflicts-array */
	ir_node **nodes;					/**< [0] is the phi node. [1..node_count-1] the arguments of the phi not interfering with it */
	conflict_t *conflicts;				/**< pairs of conflicting ir_nodes. */
	set *changed_nodes;					/**< contains node_stat_t's. */
} phi_unit_t;

static firm_dbg_module_t *dbgphi = NULL;

/**
 * Contains ir_nodes of phi-classes whose colors may change unlimited times.
 * These nodes are not optimizable, so there is no need to pin their color.
 */
static pset *free_nodes = NULL;

/**
 * Contains already optimized ir_nodes of phi-classes fully processed.
 * So one can perform a check not to switch them twice or more.
 */
static pset *pinned_global = NULL;

int set_cmp_node_stat_t(const void *x, const void *y, size_t size) {
	return ((node_stat_t *)x)->irn != ((node_stat_t *)y)->irn;
}

/**
 * Finds a node status entry of a node if existent.
 */
static INLINE node_stat_t *pu_find_node(phi_unit_t *pu, ir_node *irn) {
	node_stat_t find;
	find.irn = irn;
	return set_find(pu->changed_nodes, &find, sizeof(find), HASH_PTR(irn));
}

/**
 * Finds a node status entry of a node if existent. Otherwise it will return
 * an initialized new entry for this node.
 */
static INLINE node_stat_t *pu_find_or_insert_node(phi_unit_t *pu, ir_node *irn) {
	node_stat_t find;
	find.irn = irn;
	find.color = NO_COLOR;
	find.undo_color = NO_COLOR;
	find.status = 0;
	return set_insert(pu->changed_nodes, &find, sizeof(find), HASH_PTR(irn));
}

/**
 * @return The virtual color of a node, if set before, else just the real color.
 */
static INLINE int pu_get_new_color(phi_unit_t *pu, ir_node *irn) {
	node_stat_t *found = pu_find_node(pu, irn);
	if (found)
		return found->color;
	else
		return get_irn_color(irn);
}

/**
 * Sets the virtual color of a node.
 */
static INLINE void pu_set_new_color(phi_unit_t *pu, ir_node *irn, int color) {
	node_stat_t *found = pu_find_or_insert_node(pu, irn);
	/* TODO Think about
	 * This is only correct if no color is set >=2 times while changing
	 * a single phi-unit-member */
	found->undo_color = found->color;
	found->color = color;
}

/**
 * Checks if a node is removed from consideration respectively building
 * a maximum independent set.
 */
static INLINE int pu_is_node_removed(phi_unit_t *pu, ir_node *irn) {
	node_stat_t *found = pu_find_node(pu, irn);
	if (found)
		return _is_removed(found);
	else
		return 0;
}

/**
 * Removes a node from the base set, out of which a maximum independet
 * set gets build from.
 */
static INLINE void pu_remove_node(phi_unit_t *pu, ir_node *irn) {
	node_stat_t *found = pu_find_or_insert_node(pu, irn);
	_set_removed(found);
}

/**
 * Checks if a node is local pinned; i.e. it belongs to the same phi unit and
 * has been optimized before the current processed one.
 */
static INLINE int pu_is_node_pinned(phi_unit_t *pu, ir_node *irn) {
	node_stat_t *found = pu_find_node(pu, irn);
	if (found)
		return _is_pinned(found);
	else
		return 0;
}

/**
 * Local-pins a node, so optimizations of further nodes of the same phi unit
 * can handle situations in which a color change would undo prior optimizations.
 */
static INLINE void pu_pin_node(phi_unit_t *pu, ir_node *irn) {
	node_stat_t *found = pu_find_or_insert_node(pu, irn);
	_set_pinned(found);
}

/**
 * If a local pinned conflict occurs, a new edge in the conflict graph is added.
 * The next maximum independent set build, will regard it.
 */
static INLINE void pu_add_conflict(phi_unit_t *pu, ir_node *n1, ir_node *n2) {
	int count = pu->conflict_count;

	assert(count != 255 && "Too much conflicts. Can hold max 255 entries");
	if ((count & 15) == 0)
		pu->conflicts = realloc(pu->conflicts, (count + 16)*sizeof(*pu->conflicts));

	if ((int)n1 < (int)n2) {
		pu->conflicts[count].n1 = n1;
		pu->conflicts[count].n2 = n2;
	} else {
		pu->conflicts[count].n1 = n2;
		pu->conflicts[count].n2 = n1;
	}

	pu->conflict_count++;
}

/**
 * Checks if two nodes are in a conflict.
 */
static INLINE int pu_are_conflicting(phi_unit_t *pu, ir_node *n1, ir_node *n2) {
	const ir_node *o1, *o2;
	int i;

	if ((int)n1 < (int)n2) {
		o1 = n1;
		o2 = n2;
	} else {
		o1 = n2;
		o2 = n1;
	}

	for (i = 0; i < pu->conflict_count; ++i)
		if (pu->conflicts[i].n1 == o1 && pu->conflicts[i].n2 == o2)
			return 1;
	return 0;
}

/**
 * Determines a maximum independent set with respect to the conflict edges
 * in pu->conflicts and the nodes beeing all non-removed nodes of pu->nodes.
 * TODO: make this 'un-greedy'
 * TODO: be aware that phi nodes should find their way in the set.
 *       for 1 phi in greedy version this is no prob, cause is comes first at [0].
 */
int pu_get_max_ind_set(phi_unit_t *pu, struct obstack *res) {
	int i, o, size = 0;
	ir_node **mis;

	DBG((dbgphi, 1, "\t\t    Max indep set\n"));
	for (i = 0; i < pu->node_count; ++i) {
		int intf_det = 0;
		if (pu_is_node_removed(pu, pu->nodes[i]))
			continue;
		mis = (ir_node**) obstack_base(res);
		for (o = 0; o < size; ++o)
			if (phi_ops_interfere(pu->nodes[i], mis[o])) {
				intf_det = 1;
				break;
			}

		if (!intf_det) {
			DBG((dbgphi, 1, "\t\t\tAdding to mis %n\n", pu->nodes[i]));
			obstack_ptr_grow(res, pu->nodes[i]);
			size++;
		}
	}
	return size;
}

/**
 * Performs virtual re-coloring of node @p n to color @p col. Virtual colors of
 * other nodes are changed too, as required to preserve correctness. Function is
 * aware of local and global pinning. Recursive.
 * @param  irn The node to set the color for
 * @param  col The color to set.
 * @param  trigger The irn that caused the wish to change the color of the irn
 * @param  changed_nodes An obstack on which all ir_nodes get growed on, which are changed
 * @return CHANGE_SAVE iff setting the color is possible, with all transiteve effects.
 *         CHANGE_IMPOSSIBLE iff conflicts with reg-constraintsis occured.
 *         CHANGE_NYI iff an unhandled situation occurs.
 *         Else the first conflicting ir_node encountered is returned.
 *
 * ASSUMPTION: Assumes that a life range of a single value can't be spilt into
 * 			   several smaller intervals where other values can live in between.
 */
static ir_node *_pu_color_irn(phi_unit_t *pu, ir_node *irn, int col, const ir_node *trigger, struct obstack *changed_nodes) {
	ir_node *res;
	struct obstack confl_ob;
	ir_node **confl, *cn;
	int i, irn_col;

	obstack_init(&confl_ob);
	irn_col = pu_get_new_color(pu, irn);

	if (irn_col == col)
		goto ret_save;
	if (pset_find_ptr(pinned_global, irn) || pu_is_node_pinned(pu, irn)) {
		DBG((dbgphi, LEVEL_2, "\t\t\t%n \t~~> %n := %d: Pinned\n", trigger, irn, col));
		res = irn;
		goto ret_confl;
	}

	/* get all nodes which would conflict with this change */
	{
		struct obstack q;
		int in, out;
		ir_node *irn_bl;

		irn_bl = get_nodes_block(irn);

		/* first check for a conflicting node which is 'living in' the irns block */
		{
			ir_node *n;
			pset *live_ins = get_live_in(irn_bl);
			for (n = pset_first(live_ins); n; n = pset_next(live_ins))
				if (is_allocatable_irn(n) && n != trigger && pu_get_new_color(pu, n) == col && phi_ops_interfere(irn, n)) {
					DBG((dbgphi, LEVEL_3, "\t\t\t\t\t ******************** %n %n\n", irn, n));
					obstack_ptr_grow(&confl_ob, n);
					pset_break(live_ins);
					break;
				}
		}

		/* setup the queue of blocks */
		obstack_init(&q);
		obstack_ptr_grow(&q, irn_bl);
		in = 1;
		out = 0;

		/* process the queue */
		while (out < in) {
			ir_node *curr_bl, *sub_bl;
			int i, max;

			curr_bl = ((ir_node **)obstack_base(&q))[out++];

			/* Add to the result all nodes in the block which live in target color
			 * and interfere with the irn */
			for (i = 0, max = get_irn_n_outs(curr_bl); i < max; ++i) {
				ir_node *n = get_irn_out(curr_bl, i);
				if (is_allocatable_irn(n) && n != trigger && pu_get_new_color(pu, n) == col && phi_ops_interfere(irn, n))
					obstack_ptr_grow(&confl_ob, n);
			}

			/* If irn lives out check i-dominated blocks where the irn lives in */
			/* Fill the queue */
			if (is_live_out(curr_bl, irn)) {
				dominates_for_each(curr_bl, sub_bl)
					if (is_live_in(sub_bl, irn)) {
						obstack_ptr_grow(&q, sub_bl);
						in++;
					}
			}
		}
		obstack_free(&q, NULL);
		obstack_ptr_grow(&confl_ob, NULL);
		confl = (ir_node **) obstack_finish(&confl_ob);
	}

	/* process all nodes which would conflict with this change */
	for (i = 0, cn = confl[0]; cn; cn = confl[++i]) {
		ir_node *sub_res;

		/* try to color the conflicting node cn with the color of the irn itself */
		DBG((dbgphi, LEVEL_3, "\t\t\t%n \t~~> %n := %d: Subcheck\n", trigger, irn, col));
		sub_res = _pu_color_irn(pu, cn, irn_col, irn, changed_nodes);
		if (sub_res != CHANGE_SAVE) {
			res = sub_res;
			goto ret_confl;
		}
	}
	/* if we arrive here all sub changes can be applied, so it's save to change this irn */

ret_save:
	DBG((dbgphi, LEVEL_2, "\t\t\t%n \t~~> %n := %d: Save\n", trigger, irn, col));
	obstack_free(&confl_ob, NULL);
	pu_set_new_color(pu, irn, col);
	obstack_ptr_grow(changed_nodes, irn);
	return CHANGE_SAVE;

ret_confl:
	DBG((dbgphi, LEVEL_2, "\t\t\t%n \t~~> %n := %d: Conflict\n", trigger, irn, col));
	obstack_free(&confl_ob, NULL);
	return res;
}

#define pu_color_irn(pu,irn,col,ob) _pu_color_irn(pu, irn, col, irn, ob)

/**
 * Tries to set as much members of a phi unit as possible to color @p col.
 * All changes taken together are guaranteed to be conflict free.
 */
static int pu_try_color(phi_unit_t *pu, int col, int b_size) {
	struct obstack ob_mis, ob_undo;
	int i, redo, mis_size;
	ir_node **mis;

	/* first init pessimistically. Just return if we can't get a better result */
	mis_size = 0;

	obstack_init(&ob_mis);
	obstack_init(&ob_undo);
	redo = 1;
	while (redo) {
		redo = 0;
		/* get a max independent set regarding current conflicts */
		mis_size = pu_get_max_ind_set(pu, &ob_mis);
		mis = obstack_finish(&ob_mis);

		/* shortcut: if mis size is worse than best, then mis won't be better. */
		if (mis_size < b_size)
			goto ret;

		/* check if its possible to set the color for all members of the maximum set*/
		for (i = 0; i < mis_size; ++i) {
			ir_node *test_node, *confl_node;

			test_node = mis[i];
			DBG((dbgphi, 1, "\t\t    Testing %n\n", test_node));
			confl_node = pu_color_irn(pu, test_node, col, &ob_undo);

			if (confl_node == CHANGE_SAVE) {
				if (!pset_find_ptr(free_nodes, test_node))
					pu_pin_node(pu, test_node);
				obstack_free(&ob_undo, obstack_finish(&ob_undo));
				continue;
			} else {
				int i;
				ir_node *undo_node, **undo_nodes;

				obstack_ptr_grow(&ob_undo, NULL);
				undo_nodes = obstack_finish(&ob_undo);
				for (i = 0, undo_node = undo_nodes[0]; undo_node; undo_node = undo_nodes[++i]) {
					node_stat_t *ns = pu_find_node(pu, undo_node);
					ns->color = ns->undo_color;
				}
				obstack_free(&ob_undo, undo_nodes);

				if (is_conflicting_node(confl_node)) {
					if (pu_is_node_pinned(pu, confl_node))
						pu_add_conflict(pu, confl_node, test_node);
					if (pset_find_ptr(pinned_global, confl_node))
						pu_remove_node(pu, test_node);
				}
			}

			/* shortcut: color not possible for phi node (phi comes first) ==> exit */
			if (i == 0)
				goto ret;
		}
		obstack_free(&ob_mis, mis);
	}

ret:
	obstack_free(&ob_undo, NULL);
	obstack_free(&ob_mis, NULL);
	return mis_size;
}

/**
 * Tries to re-allocate colors of nodes in this phi unit, to achieve a lower
 * number of copy instructions placed during phi destruction. Optimized version.
 * Works only for phi-classes/phi-units with exactly 1 phi node, which is the
 * case for approximately 80% of all phi units.
 */
static void pu_coalesce_1_phi(phi_unit_t *pu) {
	int size, col, b_size, b_color;
	set *b_changes;

	/* init best search result */
	b_changes = NULL;
	b_size = 0;
	b_color = NO_COLOR;

	/* find optimum of all colors */
	for (col = MAX_COLORS-1; col >= 0; --col) {
		DBG((dbgphi, 1, "\tTrying color %d\n", col));
		size = pu_try_color(pu, col, b_size);

		/* did we find a better max ind. set? */
		if (size > b_size) {
			DBG((dbgphi, 1, "\t!! Better size: %d\n", size));
			if (b_changes)
				del_set(b_changes);
			b_changes = pu->changed_nodes;
			b_size = size;
			b_color = col;
		} else {
			del_set(pu->changed_nodes);
		}

		/* reset the phi unit to original state for next color */
		pu->changed_nodes = new_set(set_cmp_node_stat_t, INITIAL_SLOTS_CHANGED_NODES);
		pu->conflict_count = pu->conflict_count_org;

		/* shortcut: if all members can be colored we are (very) content */
		if (b_size == pu->node_count)
			break;
	}

	/* now apply the found optimum */
	if (b_changes) {
		node_stat_t *ns;
		DBG((dbgphi, 1, "\tBest color: %d  Copies: %d/%d\n", b_color, pu->node_count-b_size, pu->node_count));
		for (ns = set_first(b_changes); ns; ns = set_next(b_changes))
			set_irn_color(ns->irn, ns->color);
		free(b_changes);
	} else {
		DBG((dbgphi, 1, "\tBest color: none\n"));
	}
}

/**
 * Tries to re-allocate colors of nodes in this phi unit, to achieve a lower
 * number of copy instructions placed during phi destruction.
 * General purpose version.
 */
static void pu_coalesce_n_phi(phi_unit_t *pu) {
	DBG((dbgphi, 1, "\n"));
	/* TODO */
}

/**
 * Prepares a phi class for further processing as a phi unit.
 * @param pc The phi class to prepare.
 * @return A so called phi unit containing some prepared informations
 *         needed by the following coalescing phase.
 */
static phi_unit_t *new_pu(pset *pc) {
	phi_unit_t *pu;
	ir_node *n, *phi = NULL;

	/* get the phi count of this class */
	pu = calloc(1, sizeof(*pu));
	for (n = pset_first(pc); n; n = pset_next(pc))
		if (is_Phi(n)) {
			phi = n;
			pu->phi_count++;
		}

	if (pu->phi_count == 1) {
		ir_node **tmp;
		int i, o;
		struct obstack ob;

		obstack_init(&ob);

		/* build member set not containing phi interferers */
		DBG((dbgphi, 1, "Phi-1 class:\n"));
		pu->node_count = 1; /*for the phi*/
		for (n = pset_first(pc); n; n = pset_next(pc)) {
			if (is_Phi(n))
				continue;
			if (!phi_ops_interfere(phi, n)) {
				DBG((dbgphi, 1, "\tAdding to members: %n\n", n));
				obstack_ptr_grow(&ob, n);
				pu->node_count++;
			} else {
				DBG((dbgphi, 1, "\tPhi interferer: %n\n", n));
				pset_insert_ptr(free_nodes, n);
			}
		}
		tmp = obstack_finish(&ob);
		pu->nodes = malloc(pu->node_count * sizeof(*pu->nodes));
		pu->nodes[0] = phi;
		memcpy(&pu->nodes[1], tmp, (pu->node_count-1) * sizeof(*tmp));

		/* init conlict graph to life range interference */
		for (i = 0; i < pu->node_count; ++i)
			for (o = i+1; o < pu->node_count; ++o)
				if (phi_ops_interfere(pu->nodes[i], pu->nodes[o]))
					pu_add_conflict(pu, pu->nodes[i], pu->nodes[o]);
		pu->conflict_count_org = pu->conflict_count;

		pu->changed_nodes = new_set(set_cmp_node_stat_t, INITIAL_SLOTS_CHANGED_NODES);

		obstack_free(&ob, NULL);
	} else {
		DBG((dbgphi, 1, "Phi-n class:\n"));
		/* TODO */
	}

	DBG((dbgphi, 1, "\n"));
	return pu;
}


/**
 * Deletes a phi unit
 */
static void free_pu(phi_unit_t *pu) {
	if (pu->phi_count == 1) {
		free(pu->nodes);
		free(pu->changed_nodes);
		if (pu->conflicts)
			free(pu->conflicts);
	} else {
		/* TODO */
	}
	free(pu);
}


void be_phi_coalesce(pset *all_phi_classes) {
	pset *pc;

	pinned_global = pset_new_ptr(INITIAL_SLOTS_PINNED_GLOBAL);
	free_nodes = pset_new_ptr(INITIAL_SLOTS_FREE_NODES);

	for (pc = pset_first(all_phi_classes); pc; pc = pset_next(all_phi_classes)) {
		phi_unit_t *pu = new_pu(pc);
		if (pu->phi_count == 1)
			pu_coalesce_1_phi(pu);
		else
			pu_coalesce_n_phi(pu);
		free_pu(pu);
	}

	del_pset(free_nodes);
	del_pset(pinned_global);
}


void be_phi_coal_init(void) {
	dbgphi = firm_dbg_register("ir.be.phicoal");
	firm_dbg_set_mask(dbgphi, DEBUG_LVL);
}
