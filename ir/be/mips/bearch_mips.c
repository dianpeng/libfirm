/*
 * This file is part of libFirm.
 * Copyright (C) 2015 University of Karlsruhe.
 */

#include "be_t.h"
#include "bearch.h"
#include "bemodule.h"
#include "bera.h"
#include "gen_mips_new_nodes.h"
#include "gen_mips_regalloc_if.h"
#include "irprog_t.h"
#include "lower_dw.h"
#include "mips_emitter.h"
#include "mips_transform.h"

static int mips_is_mux_allowed(ir_node *const sel, ir_node *const mux_false, ir_node *const mux_true)
{
	(void)sel;
	(void)mux_false;
	(void)mux_true;
	return false;
}

static backend_params mips_backend_params = {
	.byte_order_big_endian         = false,
	.pic_supported                 = false,
	.unaligned_memaccess_supported = false,
	.modulo_shift                  = 32,
	.dep_param                     = NULL, // TODO
	.allow_ifconv                  = &mips_is_mux_allowed,
	.machine_size                  = 32,
	.mode_float_arithmetic         = NULL,  /* will be set later */ // TODO
	.type_long_long                = NULL,  /* will be set later */ // TODO
	.type_unsigned_long_long       = NULL,  /* will be set later */ // TODO
	.type_long_double              = NULL,  /* will be set later */ // TODO
	.stack_param_align             = 4,
	.float_int_overflow            = ir_overflow_indefinite,
};

static void mips_init(void)
{
	mips_create_opcodes();
	mips_register_init();
}

static void mips_finish(void)
{
	mips_free_opcodes();
}

static const backend_params *mips_get_libfirm_params(void)
{
	return &mips_backend_params;
}

static void mips_select_instructions(ir_graph *const irg)
{
	be_timer_push(T_CODEGEN);
	mips_transform_graph(irg);
	be_timer_pop(T_CODEGEN);
	be_dump(DUMP_BE, irg, "code-selection");

	place_code(irg);
	be_dump(DUMP_BE, irg, "place");
}

static regalloc_if_t const mips_regalloc_if = {
	.spill_cost  = 7,
	.reload_cost = 5,
	// TODO .new_spill   = mips_new_spill,
	// TODO .new_reload  = mips_new_reload,
};

static void mips_generate_code(FILE *const output, char const *const cup_name)
{
	be_begin(output, cup_name);

	foreach_irp_irg(i, irg) {
		if (!be_step_first(irg))
			continue;
		// TODO be_birg_from_irg(irg)->non_ssa_regs = sp_is_non_ssa;
		mips_select_instructions(irg);
		be_step_schedule(irg);
		be_step_regalloc(irg, &mips_regalloc_if);
		mips_emit_function(irg);
		be_step_last(irg);
	}

	be_finish();
}

static void mips_lower64(void)
{
	ir_mode *const word_unsigned = mips_reg_classes[CLASS_mips_gp].mode;
	ir_mode *const word_signed   = find_signed_mode(word_unsigned);
	lwrdw_param_t lower_dw_params = {
		// TODO .create_intrinsic = mips_create_instrinsic_fct,
		.word_unsigned    = word_unsigned,
		.word_signed      = word_signed,
		.doubleword_size  = 64,
		.big_endian       = be_is_big_endian(),
	};

	ir_prepare_dw_lowering(&lower_dw_params);
	// TODO
	ir_lower_dw_ops();
}

static void mips_lower_for_target(void)
{
	mips_lower64();
	// TODO
}

static unsigned mips_get_op_estimated_cost(ir_node const *const node)
{
#if 0 // TODO
	if (is_mips_Load(node))
		return 5;
	if (is_mips_Store(node))
		return 7;
#else
	(void)node;
#endif
	return 1;
}

static arch_isa_if_t const mips_isa_if = {
	.n_registers           = N_MIPS_REGISTERS,
	.registers             = mips_registers,
	.n_register_classes    = N_MIPS_CLASSES,
	.register_classes      = mips_reg_classes,
	.init                  = mips_init,
	.finish                = mips_finish,
	.get_params            = mips_get_libfirm_params,
	.generate_code         = mips_generate_code,
	.lower_for_target      = mips_lower_for_target,
	// TODO .is_valid_clobber      = mips_is_valid_clobber,
	.get_op_estimated_cost = mips_get_op_estimated_cost,
};

BE_REGISTER_MODULE_CONSTRUCTOR(be_init_arch_mips)
void be_init_arch_mips(void)
{
	be_register_isa_if("mips", &mips_isa_if);
}
