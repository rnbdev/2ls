/*******************************************************************\

Module: SSA Refiner for selective unwinding and inlining

Author: Peter Schrammel, Madhukar Kumar

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_SSA_REFINER_SELECTIVE_H
#define CPROVER_2LS_SSA_SSA_REFINER_SELECTIVE_H

#include "ssa_refiner.h"

#include <ssa/ssa_db.h>
#include "ssa_inliner.h"
#include "ssa_unwinder.h"

class ssa_dbt;

class ssa_refiner_selectivet:public ssa_refinert
{
public:
  struct reason_infot
  {
    // call_site; restriction:
    //  we assume that there is a single function call in an SSA node
    typedef local_SSAt::locationt function_infot;
    typedef local_SSAt::locationt loop_infot;
    std::set<function_infot> functions;
    std::set<loop_infot> loops;
  };

  class reasont:public std::map<irep_idt, reason_infot>
  {
  public:
    void merge(const reasont &other)
    {
      for(const auto &reason : other)
      {
        reason_infot &r=(*this)[reason.first];
        r.functions.insert(
          reason.second.functions.begin(),
          reason.second.functions.end());
        r.loops.insert(reason.second.loops.begin(), reason.second.loops.end());
      }
    }
  };

  ssa_refiner_selectivet(
    ssa_dbt &_ssa_db,
    ssa_unwindert &_ssa_unwinder,
    unsigned _max_unwind,
    ssa_inlinert &_ssa_inliner,
    reasont &_reason):
    ssa_db(_ssa_db),
    ssa_unwinder(_ssa_unwinder),
    max_unwind(_max_unwind),
    ssa_inliner(_ssa_inliner),
    unwind(0),
    reason(_reason)
  {
  }

  virtual bool operator()();
  virtual unsigned get_unwind() { return unwind; }

 protected:
  ssa_dbt &ssa_db;
  ssa_unwindert &ssa_unwinder;
  const unsigned max_unwind;
  ssa_inlinert &ssa_inliner;
  unsigned unwind;
  reasont &reason;
};

#endif // CPROVER_2LS_SSA_SSA_REFINER_SELECTIVE_H
