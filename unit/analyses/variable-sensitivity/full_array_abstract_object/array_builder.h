/*******************************************************************\

 Module: Unit tests helpers for arrays

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/
#ifndef CBMC_ARRAY_BUILDER_H
#define CBMC_ARRAY_BUILDER_H

full_array_abstract_objectt::full_array_pointert build_array(
  const exprt &array_expr,
  abstract_environmentt &environment,
  const namespacet &ns);

full_array_abstract_objectt::full_array_pointert build_array(
  const std::vector<int> &array,
  abstract_environmentt &environment,
  const namespacet &ns);

full_array_abstract_objectt::full_array_pointert build_top_array();

full_array_abstract_objectt::full_array_pointert build_bottom_array();

exprt read_index(
  full_array_abstract_objectt::full_array_pointert array_object,
  const index_exprt &index,
  abstract_environmentt &environment,
  const namespacet &ns);

#endif //CBMC_ARRAY_BUILDER_H
