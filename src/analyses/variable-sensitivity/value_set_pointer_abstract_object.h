/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set of Pointer Abstract Object

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H

#include <analyses/variable-sensitivity/abstract_pointer_object.h>
#include <analyses/variable-sensitivity/abstract_object_set.h>

class value_set_pointer_abstract_objectt : public abstract_pointer_objectt,
                                           public value_set_tag
{
public:
  /// \copydoc abstract_objectt::abstract_objectt(const typet&)
  explicit value_set_pointer_abstract_objectt(const typet &type);

  /// \copydoc abstract_objectt::abstract_objectt(const typet &, bool, bool)
  value_set_pointer_abstract_objectt(const typet &type, bool top, bool bottom);

  value_set_pointer_abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  /// \copydoc abstract_objectt::to_constant
  exprt to_constant() const override
  {
    verify();
    return values.size() == 1 ? (*values.begin())->to_constant()
                              : abstract_objectt::to_constant();
  }

  /// Getter for the set of stored abstract objects.
  /// \return the values represented by this abstract object
  const abstract_object_sett &get_values() const override
  {
    return values;
  }

  /// Setter for updating the stored values
  /// \param other_values: the new (non-empty) set of values
  void set_values(const abstract_object_sett &other_values);

  /// The threshold size for value-sets: past this threshold the object is
  /// either converted to interval or marked as `top`.
  static const size_t max_value_set_size = 10;

  void output(std::ostream &out, const ai_baset &ai, const namespacet &ns)
    const override;

protected:
  CLONE

  /// \copydoc abstract_object::merge
  abstract_object_pointert merge(abstract_object_pointert other) const override;

private:
  /// Update the set of stored values to \p new_values. Build a new abstract
  ///   object of the right type if necessary.
  /// \param new_values: potentially new set of values
  /// \param environment: the abstract environment
  /// \return the abstract object representing \p new_values (either 'this' or
  ///   something new)
  abstract_object_pointert resolve_new_values(
    const abstract_object_sett &new_values,
    const abstract_environmentt &environment) const;

  /// Update the set of stored values to \p new_values. Build a new abstract
  ///   object of the right type if necessary.
  /// \param new_values: potentially new set of values
  /// \return the abstract object representing \p new_values (either 'this' or
  ///   something new)
  abstract_object_pointert
  resolve_values(const abstract_object_sett &new_values) const;

  // data
  abstract_object_sett values;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_VALUE_SET_POINTER_ABSTRACT_OBJECT_H
