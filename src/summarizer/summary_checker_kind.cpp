/*******************************************************************\

Module: Summarizer Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_kind.h"

#define GIVE_UP_INVARIANTS 7

/*******************************************************************\

Function: summary_checker_kindt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_kindt::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  irep_idt entry_function = goto_model.goto_functions.entry_point();
  if(options.get_bool_option("unit-check"))
     entry_function = "";

  SSA_functions(goto_model,ns);

  ssa_unwinder.init(true,false);

  property_checkert::resultt result = property_checkert::UNKNOWN;
  unsigned max_unwind = options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind = 0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << eom;
    summary_db.mark_recompute_all(); //TODO: recompute only functions with loops
    //ssa_unwinder.unwind_all(unwind);

    // unwind loops "selectively" (those that seem to be the "reason")
    for(summarizer_bw_cex_baset::reasont::const_iterator it = reason.begin(); it != reason.end(); ++it){
      for(std::set<summarizer_bw_cex_baset::reason_infot::loop_infot>::const_iterator l_it = it->second.loops.begin();
	  l_it != it->second.loops.end(); l_it++){
	ssa_unwinder.unwind_loop_alone(it->first, (*l_it)->location_number, unwind);
      }
    }

    // inline functions "selectively" (those that seem to be the "reason")
    for(summarizer_bw_cex_baset::reasont::const_iterator it = reason.begin(); it != reason.end(); ++it){
      for(std::set<summarizer_bw_cex_baset::reason_infot::function_infot>::const_iterator f_it = it->second.functions.begin();
	  f_it != it->second.functions.end(); f_it++){
	local_SSAt &SSA = ssa_db.get(it->first);

	for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin();
	    n_it != SSA.nodes.end(); n_it++){

	  local_SSAt::nodet &node=*n_it;
	  if(node.location == *(f_it)){

	    for(local_SSAt::nodet::function_callst::const_iterator fc_it=node.function_calls.begin();
		fc_it!=node.function_calls.end(); fc_it++){
	      
	      irep_idt fname = to_symbol_expr(fc_it->function()).get_identifier();
	      if(ssa_db.exists(fname))
		{
		  const local_SSAt &fSSA = ssa_db.get(fname);

		  exprt guard_binding;
		  exprt::operandst bindings_in, bindings_out;
		  int counter = ssa_inliner.get_rename_counter();

		  ssa_inliner.get_guard_binding(SSA,fSSA,n_it,guard_binding,counter);
		  equal_exprt e = to_equal_expr(guard_binding);
		  node.equalities.push_back(e);
		  
		  
		  ssa_inliner.get_bindings(SSA,fSSA,n_it,fc_it,bindings_in,bindings_out,counter);
		  // put guard_binding, bindings_in, bindings_out in the caller's SSA (equalities)

		  // copy fSSA's each node's items (equalities, assertions, etc.)
		  // into node's corresponding item (after renaming)

		  
		  
		}
		  
		  
	    }
	  }
	}


	
	
      }
    }

    //dependency graphs
    if(!(options.get_bool_option("inline")))
    {
      if((options.get_option("spurious-check")!="concrete") &&
	 (options.get_option("spurious-check")!="abstract"))
      {
	SSA_dependency_graphs(goto_model, ns);
      }
    }
    
    std::set<irep_idt> seen_function_calls;
    result =  check_properties(entry_function, entry_function, seen_function_calls); 
    if(result == property_checkert::UNKNOWN &&
       !options.get_bool_option("havoc") && 
       (unwind<GIVE_UP_INVARIANTS || 
        !options.get_bool_option("competition-mode"))) //magic constant 
    {
      summarize(goto_model);
      std::set<irep_idt> seen_function_calls;
      result =  check_properties(entry_function, entry_function, seen_function_calls); 
    }

    if(result == property_checkert::PASS) 
    {
      status() << "k-induction proof found after " 
	       << unwind << " unwinding(s)" << eom;
      break;
    }
    else if(result == property_checkert::FAIL) 
    {
      status() << "k-induction counterexample found after " 
	       << unwind << " unwinding(s)" << eom;
      break;
    }
  }
  report_statistics();
  return result;
}

