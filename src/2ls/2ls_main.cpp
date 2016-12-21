/*******************************************************************\

Module: 2LS Main Module

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

#include <util/unicode.h>

#include "2ls_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  twols_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
#else
int main(int argc, const char **argv)
{
  twols_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
#endif
