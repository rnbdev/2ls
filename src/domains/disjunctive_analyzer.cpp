/*******************************************************************\

Module: Data Flow Analysis

Author: Peter Schrammel, Kumar Madhukar

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/find_symbols.h>

#include "ssa_analyzer.h"
#include "disjunctive_analyzer.h"

/*******************************************************************\

Function: disjunctive_analyzert::eliminate_implication()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_analyzert::eliminate_implication(exprt &formula)
{
  if(formula.id()==ID_implies)
    formula=or_exprt(not_exprt(formula.op0()), formula.op1());

  Forall_operands(it, formula)
    eliminate_implication(*it);
}

/*******************************************************************\

Function: disjunctive_analyzert::push_negation_to_atoms()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_analyzert::push_negation_to_atoms(exprt &formula)
{
  if(formula.id()==ID_not)
  {
    if((formula.op0()).id()==ID_not)
    {
      formula=(formula.op0()).op0();
    }
    else
    {
      exprt::operandst operands;
      Forall_operands(it, formula.op0())
        operands.push_back(not_exprt(*it));

      if((formula.op0()).id()==ID_and)
      {
        formula=disjunction(operands);
      }
      else
      {
        if((formula.op0()).id()==ID_or)
        {
          formula=conjunction(operands);
        }
      }
    }
  }

  Forall_operands(it, formula)
    push_negation_to_atoms(*it);
}

/*******************************************************************\

Function: disjunctive_analyzert::convert_to_dnf()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_analyzert::convert_to_dnf(exprt &formula)
{
  eliminate_implication(formula);
  push_negation_to_atoms(formula);
  convert_to_dnf_rec(formula);
}

/*******************************************************************\

Function: disjunctive_analyzert::convert_to_dnf_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void disjunctive_analyzert::convert_to_dnf_rec(exprt &formula)
{
  if(formula.id()==ID_or)
  {
    Forall_operands(it, formula)
      convert_to_dnf_rec(*it);
  }
  else
  {
    if(formula.id()==ID_and)
    {
      Forall_operands(it, formula)
        convert_to_dnf_rec(*it);

      while((formula.operands()).size()>1)
      {
        exprt::operandst first_operands, second_operands, combination;

        if(((formula.operands()).back()).id()==ID_or)
          first_operands=((formula.operands()).back()).operands();
        else
          first_operands.push_back((formula.operands()).back());
        formula.operands().pop_back();

        if(((formula.operands()).back()).id()==ID_or)
          second_operands=((formula.operands()).back()).operands();
        else
          second_operands.push_back((formula.operands()).back());
        formula.operands().pop_back();

        for(const auto &fo : first_operands)
        {
          for(const auto &so : second_operands)
          {
            combination.push_back(and_exprt(fo, so));
          }
        }

        formula.operands().push_back(disjunction(combination));
      }
      formula=formula.op0();
    }
  }
}

/*******************************************************************\

Function: disjunctive_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool disjunctive_analyzert::operator()(
  incremental_solvert &solver,
  local_SSAt &SSA,
  const exprt &side_conditions,
  template_generator_baset &template_generator,
  const exprt &disjunctive_conditions,
  exprt &result_expr,
  const domaint::var_sett &vars)
{
  bool response=true;
  exprt::operandst result;

  exprt simple_disjunctive_conditions=
    simplify_expr(disjunctive_conditions, SSA.ns); // disjunctive_conditions

  // converting simple_disjunctive_conditions into DNF
  convert_to_dnf(simple_disjunctive_conditions);

  if(simple_disjunctive_conditions.id()==ID_or)
  {
    exprt::operandst processed_disjuncts;

    exprt::operandst disjuncts=simple_disjunctive_conditions.operands();
    for(auto &d : disjuncts)
    {
      if(d.id()==ID_not)
      {
        exprt::operandst ops=d.operands();
        for(auto &op : ops)
        {
          if(op.id()==ID_equal)
          {
            exprt::operandst ops_equality=op.operands();
            equal_exprt equal_expr_in_not=to_equal_expr(op);

            bool constant_comparison=false;
            for(auto &oe : ops_equality)
            {
              if(oe.id()==ID_constant)
                constant_comparison=true;
            }
            if(constant_comparison)
            {
              processed_disjuncts.push_back(
                binary_relation_exprt(
                  equal_expr_in_not.rhs(), ID_gt, equal_expr_in_not.lhs()));
              processed_disjuncts.push_back(
                binary_relation_exprt(
                  equal_expr_in_not.rhs(), ID_lt, equal_expr_in_not.lhs()));
            }
            else
            {
              processed_disjuncts.push_back(d);
            }
          }
          else
          {
            processed_disjuncts.push_back(d);
          }
        }
      }
      else
      {
        processed_disjuncts.push_back(d);
      }
    }

    for(auto &d : processed_disjuncts)
    {
      std::set<symbol_exprt> disjunct_symbols;
      find_symbols(d, disjunct_symbols);

      // TODO: decompose into convex regions for all variables
      // assert(disjunct_symbols.size()==1);

      // TODO: unclear what this loop should be doing
      symbol_exprt var;
      for(const auto &ds : disjunct_symbols)
      {
        var=ds;
      }

      exprt::operandst split_disjuncts;

      if((var.type().id()==ID_signedbv) || (var.type().id()==ID_unsignedbv))
      {
        exprt smallest;
        if(var.type().id()==ID_signedbv)
          smallest=to_signedbv_type(var.type()).smallest_expr();
        if(var.type().id()==ID_unsignedbv)
          smallest=to_unsignedbv_type(var.type()).smallest_expr();

        split_disjuncts.push_back(
          and_exprt(
            d,
            binary_relation_exprt(
              var,
              ID_ge,
              plus_exprt(smallest, from_integer(mp_integer(1), var.type())))));

        split_disjuncts.push_back(
          and_exprt(d, binary_relation_exprt(var, ID_equal, smallest)));
      }
      else
      {
        split_disjuncts.push_back(d);
      }

      for(auto &sd : split_disjuncts)
      {
        ssa_analyzert analyzer;
        analyzer.set_message_handler(get_message_handler());
        exprt cc=simplify_expr((and_exprt(side_conditions, sd)), SSA.ns);
        response=response && (analyzer(solver, SSA, cc, template_generator));

        exprt res;
        analyzer.get_result(res, vars);
        result.push_back(res);

        // statistics
        solver_instances+=analyzer.get_number_of_solver_instances();
        solver_calls+=analyzer.get_number_of_solver_calls();
      }
    }
  }
  else
  {
    // for the complete disjunctive_conditions at once
    ssa_analyzert analyzer;
    analyzer.set_message_handler(get_message_handler());
    exprt cc=simplify_expr(
      and_exprt(side_conditions, simple_disjunctive_conditions), SSA.ns);

    response=analyzer(solver, SSA, cc, template_generator);

    exprt res;
    analyzer.get_result(res, vars);
    result.push_back(res);

    // statistics
    solver_instances+=analyzer.get_number_of_solver_instances();
    solver_calls+=analyzer.get_number_of_solver_calls();
  }

  result_expr=disjunction(result);
  return response;
}

