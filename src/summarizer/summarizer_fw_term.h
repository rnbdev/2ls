/*******************************************************************\

Module: Summarizer for Forward Analysis

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_FW_TERM_H
#define CPROVER_SUMMARIZER_FW_TERM_H

#include <util/message.h>
#include <util/options.h>

#include "summarizer_fw.h"

#include "../ssa/ssa_inliner.h"
#include "../ssa/ssa_unwinder.h"
#include "../ssa/local_ssa.h"
#include "ssa_db.h"

#include <util/time_stopping.h>

class summarizer_fw_termt : public summarizer_fwt
{
 public:
 explicit summarizer_fw_termt(optionst &_options, 
	     summary_dbt &_summary_db,
             ssa_dbt &_ssa_db,
	     ssa_unwindert &_ssa_unwinder,
	     ssa_inlinert &_ssa_inliner) : 
  summarizer_fwt(_options,_summary_db,_ssa_db,_ssa_unwinder,_ssa_inliner)
  {}

 protected:

  virtual void compute_summary_rec(const function_namet &function_name,
    		           const exprt &precondition,
                           bool context_sensitive);

  void inline_summaries(const function_namet &function_name, 
			local_SSAt &SSA,
    		        exprt precondition,
                        bool context_sensitive,
			threevalt &calls_terminate,
			bool &has_function_calls); 

  void do_termination(const function_namet &function_name, 
		      const local_SSAt &SSA, 
		      summaryt &summary);

  threevalt check_termination_argument(exprt expr);

  bool check_end_reachable(const function_namet &function_name,
			   const local_SSAt &SSA, 
			   const exprt &cond);
};


#endif
