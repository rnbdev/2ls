/*******************************************************************\

Module: Counterexample-based Backward Analysis

Author: Kumar Madhukar, Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>
#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/find_symbols.h>

#include "summarizer_bw_cex.h"
#include "summary_db.h"

#include <domains/ssa_analyzer.h>
#include <domains/template_generator_summary.h>
#include <domains/template_generator_callingcontext.h>

#include <ssa/local_ssa.h>
#include <ssa/simplify_ssa.h>


/*******************************************************************\

Function: summarizer_bw_cex_baset::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_baset::summarize()
{
  assert(false); // unused
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_bw_cex_baset::summarize(const function_namet &function_name)
{
  exprt postcondition=true_exprt(); // initial calling context

  status() << "\nSummarizing function " << function_name << eom;
  compute_summary_rec(function_name, postcondition, true);
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::summarize()

  Inputs:

 Outputs:

 Purpose: summarize backwards from given assertion

\*******************************************************************/

void summarizer_bw_cex_baset::summarize(const exprt &_error_assertion)
{
  status() << "\nBackward error analysis..." << eom;
  error_assertion=_error_assertion;

  summarize(entry_function);
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::check()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summarizer_bw_cex_baset::check()
{
  assert(false);
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::get_loophead_selects

  Inputs:

 Outputs:

 Purpose: returns the select guards at the loop heads
          in order to check whether a countermodel is spurious

\*******************************************************************/

void summarizer_bw_cex_baset::get_loophead_selects(
  const irep_idt &function_name,
  const local_SSAt &SSA,
  prop_convt &solver,
  exprt::operandst &loophead_selects)
{
  // TODO: this should be provided by unwindable_local_SSA
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead==SSA.nodes.end())
      continue;
    symbol_exprt lsguard=
      SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
    ssa_unwinder.get(function_name).unwinder_rename(lsguard, *n_it, true);
    loophead_selects.push_back(not_exprt(lsguard));
    solver.set_frozen(solver.convert(lsguard));
  }
  literalt loophead_selects_literal=
    solver.convert(conjunction(loophead_selects));
  if(!loophead_selects_literal.is_constant())
    solver.set_frozen(loophead_selects_literal);

#if 0
  std::cout << "loophead_selects: "
            << from_expr(SSA.ns, "", conjunction(loophead_selects))
            << std::endl;
#endif
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::get_loop_continues

  Inputs:

 Outputs:

 Purpose: returns the loop continuation guards at the end of the
          loops in order to check whether we can unroll further

\*******************************************************************/

void summarizer_bw_cex_baset::get_loop_continues(
  const irep_idt &function_name,
  const local_SSAt &SSA,
  prop_convt &solver,
  exprt::operandst &loop_continues)
{
  // TODO: this should be provided by unwindable_local_SSA
  ssa_unwinder.get(function_name).loop_continuation_conditions(loop_continues);
  if(loop_continues.size()==0)
  {
    // TODO: this should actually be done transparently by the unwinder
    for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
        n_it!=SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end())
        continue;
      symbol_exprt guard=SSA.guard_symbol(n_it->location);
      symbol_exprt cond=SSA.cond_symbol(n_it->location);
      loop_continues.push_back(and_exprt(guard, cond));
    }
  }

#if 0
  std::cout << "loophead_continues: "
            << from_expr(SSA.ns, "", disjunction(loop_continues)) << std::endl;
#endif
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::get_loop_continues

  Inputs:

 Outputs:

 Purpose: returns the loop continuation guards at the end of the
          given loop in order to check whether we can unroll further

\*******************************************************************/

void summarizer_bw_cex_baset::get_loop_continues(
  const irep_idt &function_name,
  const local_SSAt &SSA,
  const local_SSAt::locationt &loop_id,
  exprt::operandst &loop_continues)
{
  // TODO: need to ask ssa_inliner regarding inlined functions

  // TODO: this should be provided by unwindable_local_SSA

  ssa_unwinder.get(function_name)
    .loop_continuation_conditions(loop_id, loop_continues);
  if(loop_continues.empty())
  {
    // TODO: this should actually be done transparently by the unwinder
    for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
  n_it!=SSA.nodes.end(); n_it++)
    {
      if(n_it->loophead==SSA.nodes.end())
        continue;
      if(n_it->loophead->location!=loop_id)
        continue;
      symbol_exprt guard=SSA.guard_symbol(n_it->location);
      symbol_exprt cond=SSA.cond_symbol(n_it->location);
      loop_continues.push_back(and_exprt(guard, cond));
      break;
    }
  }

#if 0
  std::cout << "loophead_continues: "
            << from_expr(SSA.ns, "", disjunction(loop_continues)) << std::endl;
#endif
}

/*******************************************************************\

Function: summarizer_bw_cex_baset::is_fully_unwound

  Inputs:

 Outputs:

 Purpose: checks whether the loops have been fully unwound

\*******************************************************************/

bool summarizer_bw_cex_baset::is_fully_unwound(
  const exprt::operandst &loop_continues,
  const exprt::operandst &loophead_selects,
  incremental_solvert &solver)
{
  solver.new_context();
  solver <<
    and_exprt(conjunction(loophead_selects), disjunction(loop_continues));

  solver_calls++; // statistics

  switch(solver())
  {
  case decision_proceduret::D_SATISFIABLE:
    solver.pop_context();
    return false;
    break;

  case decision_proceduret::D_UNSATISFIABLE:
    solver.pop_context();
    solver << conjunction(loophead_selects);
    return true;
    break;

  case decision_proceduret::D_ERROR:
  default:
    throw "error from decision procedure";
  }
}
