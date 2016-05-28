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

	std::list<local_SSAt::nodet> inline_nodes;
	std::vector<equal_exprt> first_node_equalities;
	int counter = ssa_inliner.get_rename_counter();
	
	for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin();
	    n_it != SSA.nodes.end(); n_it++){
	  
	  local_SSAt::nodet &node=*n_it;

	  if(node.location == *(f_it)){

	    bool clear_function_call = false;
	    
	    for(local_SSAt::nodet::function_callst::const_iterator fc_it=node.function_calls.begin();
		fc_it!=node.function_calls.end(); fc_it++){
	      
	      irep_idt fname = to_symbol_expr(fc_it->function()).get_identifier();
	      if(ssa_db.exists(fname))
		{
		  clear_function_call = true;
		  
		  local_SSAt &fSSA = ssa_db.get(fname);

		  exprt guard_binding;
		  exprt::operandst bindings_in, bindings_out;
			  
		  // put guard_binding, bindings_in, bindings_out in the caller's SSA (equalities)
		  ssa_inliner.get_guard_binding(SSA,fSSA,n_it,guard_binding,counter);
		  equal_exprt e = to_equal_expr(guard_binding);
		  node.equalities.push_back(e);
		  
		  ssa_inliner.get_bindings(SSA,fSSA,n_it,fc_it,bindings_in,bindings_out,counter);

		  for(exprt::operandst::const_iterator b_it=bindings_in.begin();
		      b_it!=bindings_in.end(); b_it++){
		    equal_exprt e = to_equal_expr(*b_it);
		    node.equalities.push_back(e);
		  }
		  for(exprt::operandst::const_iterator b_it=bindings_out.begin();
		      b_it!=bindings_out.end(); b_it++){
		    equal_exprt e = to_equal_expr(*b_it);
		    node.equalities.push_back(e);
		  }

		  for(local_SSAt::nodest::const_iterator fn_it = fSSA.nodes.begin();
		      fn_it != fSSA.nodes.end(); fn_it++){
		    local_SSAt::nodet fnode=*fn_it;
		    inline_nodes.push_back(fnode);
		  }

		  if(fname == entry_function){
		    //  first_node_equalities should contain all the equalities from the first node of fSSA
		    for(local_SSAt::nodest::iterator fn_it = fSSA.nodes.begin();
			fn_it != fSSA.nodes.end(); fn_it++){
		      local_SSAt::nodet &fnode=*fn_it;
		      for(local_SSAt::nodet::equalitiest::iterator e_it=fnode.equalities.begin();
			  e_it!=fnode.equalities.end(); e_it++){
			first_node_equalities.push_back(*e_it);
		      }
		      break;
		    }
		  }
		  else{
		    //  except those (the one) that start with "ssa::guard" and have true in the rhs
		    for(local_SSAt::nodest::iterator fn_it = fSSA.nodes.begin();
			fn_it != fSSA.nodes.end(); fn_it++){
		      local_SSAt::nodet &fnode=*fn_it;

		      bool ignore_equality = true;
		      
		      for(local_SSAt::nodet::equalitiest::iterator e_it=fnode.equalities.begin();
			  e_it!=fnode.equalities.end(); e_it++){
			// unless lhs starts with "ssa::guard" and rhs is true

			equal_exprt e = to_equal_expr(*e_it);
			exprt &lhs = e.lhs(); exprt &rhs = e.rhs();
			std::string var_string = id2string(to_symbol_expr(lhs).get_identifier());
			if(((var_string.substr(0,11)) == "ssa::$guard") && (rhs.is_true()) && (ignore_equality == true)){
			  ignore_equality = false;
			}
			else{
			  first_node_equalities.push_back(*e_it);
			}
			
		      }
		      break;
		    }
		  }

		}
	    }
	    
	    if(clear_function_call == true)
	      node.function_calls.clear();
		
	  }
	}

	bool replace_first_node_equalities = true;
	
	if(inline_nodes.size() > 0){
	  for(std::list<local_SSAt::nodet>::iterator in_it = inline_nodes.begin();
	      in_it != inline_nodes.end(); in_it++){
	    local_SSAt::nodet &inline_node = *in_it;

	    if(replace_first_node_equalities == true){
	      inline_node.equalities.clear();
	      for(std::vector<equal_exprt>::iterator e_it=first_node_equalities.begin();
		  e_it!=first_node_equalities.end(); e_it++){
		inline_node.equalities.push_back(*e_it);
	      }
	      replace_first_node_equalities = false;
	    }
	    
	    for(local_SSAt::nodet::equalitiest::iterator e_it=inline_node.equalities.begin();
		e_it!=inline_node.equalities.end(); e_it++){
	      ssa_inliner.rename(*e_it, counter);
	    }
	    
	    for(local_SSAt::nodet::constraintst::iterator c_it=inline_node.constraints.begin();
		c_it!=inline_node.constraints.end(); c_it++){
	      ssa_inliner.rename(*c_it, counter);
	    }

	    for(local_SSAt::nodet::assertionst::iterator a_it=inline_node.assertions.begin();
		a_it!=inline_node.assertions.end(); a_it++){
	      ssa_inliner.rename(*a_it, counter);
	    }

	    // push inline_node into SSA
	    SSA.nodes.push_back(inline_node);
	    
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

