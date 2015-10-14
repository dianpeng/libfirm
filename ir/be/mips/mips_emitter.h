/*
 * This file is part of libFirm.
 * Copyright (C) 2015 University of Karlsruhe.
 */

/**
 * @file
 * @brief       This file implements the mips node emitter.
 * @author      Christoph Mallon
 */
#ifndef FIRM_BE_MIPS_IA32_EMITTER_H
#define FIRM_BE_MIPS_IA32_EMITTER_H

#include "irnode.h"

/**
 * fmt  parameter               output
 * ---- ----------------------  ---------------------------------------------
 * %%                           %
 * %Sx  <node>                  source register x
 *
 * x starts at 0
 */
void mips_emitf(ir_node const *node, char const *fmt, ...);

void mips_emit_function(ir_graph *irg);

void mips_init_emitter(void); // TODO

#endif
