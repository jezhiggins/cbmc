/*******************************************************************\

Module: Local variables

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

/// \file
/// Local variables

#include "locals.h"

#include <util/std_expr.h>

void localst::build(const goto_functiont &goto_function)
{
  for(const auto &instruction : goto_function.body.instructions)
  {
    if(instruction.is_decl())
      locals.insert(instruction.decl_symbol().get_identifier());
  }

  locals.insert(
    goto_function.parameter_identifiers.begin(),
    goto_function.parameter_identifiers.end());
}

void localst::output(std::ostream &out) const
{
  for(const auto &local : locals)
    out << local << "\n";
}
