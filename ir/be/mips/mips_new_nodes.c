/*
 * This file is part of libFirm.
 * Copyright (C) 2015 University of Karlsruhe.
 */

#include "mips_new_nodes.h"

#include <inttypes.h>

#include "gen_mips_new_nodes.h"
#include "ircons_t.h"

static int mips_attrs_equal_(mips_attr_t const *const a_attr, mips_attr_t const *const b_attr)
{
#if 0
	return except_attrs_equal(&a_attr->exc, &b_attr->exc); // TODO all other backends do not check this either
#else
	(void)a_attr, (void)b_attr;
	return 1;
#endif
}

static int mips_attrs_equal(ir_node const *const a, ir_node const *const b)
{
	mips_attr_t const *const a_attr = get_mips_attr_const(a);
	mips_attr_t const *const b_attr = get_mips_attr_const(b);
	return mips_attrs_equal_(a_attr, b_attr);
}

static int mips_cond_attrs_equal(ir_node const *const a, ir_node const *const b)
{
	mips_cond_attr_t const *const a_attr = get_mips_cond_attr_const(a);
	mips_cond_attr_t const *const b_attr = get_mips_cond_attr_const(b);
	return
		mips_attrs_equal_(&a_attr->attr, &b_attr->attr) &&
		a_attr->cond == b_attr->cond;
}

static int mips_immediate_attrs_equal(ir_node const *const a, ir_node const *const b)
{
	mips_immediate_attr_t const *const a_attr = get_mips_immediate_attr_const(a);
	mips_immediate_attr_t const *const b_attr = get_mips_immediate_attr_const(b);
	return
		mips_attrs_equal_(&a_attr->attr, &b_attr->attr) &&
		a_attr->ent == b_attr->ent &&
		a_attr->val == b_attr->val;
}

static void dump_immediate(FILE *const F, char const *const prefix, ir_node const *const n)
{
	mips_immediate_attr_t const *const imm = get_mips_immediate_attr_const(n);
	if (imm->ent) {
		fputc(' ', F);
		if (prefix)
			fprintf(F, "%s(", prefix);
		fputs(get_entity_name(imm->ent), F);
		if (imm->val != 0)
			fprintf(F, "%+" PRId32, imm->val);
		if (prefix)
			fputc(')', F);
	} else {
		fprintf(F, " %+" PRId32, imm->val);
	}
}

static void mips_dump_node(FILE *const F, ir_node const *const n, dump_reason_t const reason)
{
	switch (reason) {
		case dump_node_opcode_txt:
			fprintf(F, "%s", get_irn_opname(n));
			if (is_mips_addiu(n) || is_mips_lw(n) || is_mips_sw(n)) {
				dump_immediate(F, "%lo", n);
			} else if (is_mips_andi(n) || is_mips_ori(n) || is_mips_xori(n)) {
				mips_immediate_attr_t const *const imm = get_mips_immediate_attr_const(n);
				fprintf(F, " 0x%04" PRIX32, (uint32_t)imm->val);
			} else if (is_mips_jal(n)) {
				dump_immediate(F, NULL, n);
			} else if (is_mips_lui(n)) {
				dump_immediate(F, "%hi", n);
			}
			break;

		case dump_node_mode_txt:
			break;

		case dump_node_nodeattr_txt:
			break;

		case dump_node_info_txt:
			break;
	}
}

#include "gen_mips_new_nodes.c.inl"
