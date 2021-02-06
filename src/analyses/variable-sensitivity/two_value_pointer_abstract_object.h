/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_TWO_VALUE_POINTER_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_TWO_VALUE_POINTER_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_pointer_object.h>

class two_value_pointer_abstract_objectt : public abstract_pointer_objectt
{
public:
  /// \param type: the type the abstract_object is representing
  explicit two_value_pointer_abstract_objectt(const typet &type)
    : abstract_pointer_objectt(type)
  {
  }

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  two_value_pointer_abstract_objectt(const typet &type, bool top, bool bottom)
    : abstract_pointer_objectt(type, top, bottom)
  {
  }

  /// \param expr: the expression to use as the starting pointer for
  ///              an abstract object
  /// \param environment: the environment in which the pointer is being
  ///                     created
  /// \param ns: the current namespace
  two_value_pointer_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : abstract_pointer_objectt(expr, environment, ns)
  {
  }
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_TWO_VALUE_POINTER_ABSTRACT_OBJECT_H
