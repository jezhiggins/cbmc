/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: diffblue

\*******************************************************************/

/// \file
/// Value Set Abstract Object

#include "interval_abstract_value.h"
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/context_abstract_object.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>

#include <util/make_unique.h>

#include "abstract_environment.h"

static index_range_implementation_ptrt
make_value_set_index_range(const std::set<exprt> &vals);

class value_set_index_ranget : public index_range_implementationt
{
public:
  explicit value_set_index_ranget(const std::set<exprt> &vals)
    : values(vals), cur(), next(values.begin())
  {
    PRECONDITION(!values.empty());
  }

  const exprt &current() const override
  {
    return cur;
  }
  bool advance_to_next() override
  {
    if(next == values.end())
      return false;

    cur = *next;
    ++next;
    return true;
  }
  index_range_implementation_ptrt reset() const override
  {
    return make_value_set_index_range(values);
  }

private:
  std::set<exprt> values;
  exprt cur;
  std::set<exprt>::const_iterator next;
};

static index_range_implementation_ptrt
make_value_set_index_range(const std::set<exprt> &vals)
{
  return util_make_unique<value_set_index_ranget>(vals);
}

static value_range_implementation_ptrt
make_value_set_value_range(const abstract_object_sett &vals);

class value_set_value_ranget : public value_range_implementationt
{
public:
  explicit value_set_value_ranget(const abstract_object_sett &vals)
    : values(vals), cur(), next(values.begin())
  {
    PRECONDITION(!values.empty());
  }

  const abstract_object_pointert &current() const override
  {
    return cur;
  }
  bool advance_to_next() override
  {
    if(next == values.end())
      return false;

    cur = *next;
    ++next;
    return true;
  }
  value_range_implementation_ptrt reset() const override
  {
    return make_value_set_value_range(values);
  }

private:
  const abstract_object_sett &values;
  abstract_object_pointert cur;
  abstract_object_sett::const_iterator next;
};

static value_range_implementation_ptrt
make_value_set_value_range(const abstract_object_sett &vals)
{
  return util_make_unique<value_set_value_ranget>(vals);
}

static abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values);

/// Helper for converting singleton value sets into its only value.
/// \p maybe_singleton: either a set of abstract values or a single value
/// \return an abstract value without context
static abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton);

static bool are_any_top(const abstract_object_sett &set);

value_set_abstract_objectt::value_set_abstract_objectt(const typet &type)
  : abstract_value_objectt(type)
{
  values.insert(std::make_shared<constant_abstract_valuet>(type));
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const typet &type,
  bool top,
  bool bottom)
  : abstract_value_objectt(type, top, bottom)
{
  values.insert(std::make_shared<constant_abstract_valuet>(type, top, bottom));
  verify();
}

value_set_abstract_objectt::value_set_abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : abstract_value_objectt(expr.type(), false, false)
{
  values.insert(
    std::make_shared<constant_abstract_valuet>(expr, environment, ns));
  verify();
}

index_range_implementation_ptrt
value_set_abstract_objectt::index_range_implementation(
  const namespacet &ns) const
{
  if(values.empty())
    return make_indeterminate_index_range();

  std::set<exprt> flattened;
  for(const auto &o : values)
  {
    const auto &v = std::dynamic_pointer_cast<const abstract_value_objectt>(o);
    for(auto e : v->index_range(ns))
      flattened.insert(e);
  }

  return make_value_set_index_range(flattened);
}

value_range_implementation_ptrt
value_set_abstract_objectt::value_range_implementation() const
{
  return make_value_set_value_range(values);
}

exprt value_set_abstract_objectt::to_constant() const
{
  verify();

  if(values.size() == 1)
    return values.first()->to_constant();

  auto interval = to_interval();
  if(interval.is_single_value_interval())
    return interval.get_lower();

  return abstract_objectt::to_constant();
}

constant_interval_exprt value_set_abstract_objectt::to_interval() const
{
  return values.to_interval();
}

abstract_object_pointert value_set_abstract_objectt::merge_with_value(
  const abstract_value_pointert &other,
  const wident &widen_mode) const
{
  auto union_values = !is_bottom() ? values : abstract_object_sett{};

  auto other_value_set = std::dynamic_pointer_cast<const value_set_tag>(other);
  if(other_value_set)
    union_values.insert(other_value_set->get_values());
  else
    union_values.insert(other);

  return resolve_values(union_values);
}

abstract_object_pointert value_set_abstract_objectt::meet_with_value(
  const abstract_value_pointert &other) const
{
  if(other->is_bottom())
    return shared_from_this();

  auto meet_values = abstract_object_sett{};

  if(is_bottom())
    meet_values.insert(other);
  else
  {
    auto this_interval = to_interval();
    auto other_interval = other->to_interval();

    auto lower_bound = constant_interval_exprt::get_max(
      this_interval.get_lower(), other_interval.get_lower());
    auto upper_bound = constant_interval_exprt::get_min(
      this_interval.get_upper(), other_interval.get_upper());

    // if the interval is valid, we have a meet!
    if(constant_interval_exprt::less_than_or_equal(lower_bound, upper_bound))
    {
      auto meet_interval = constant_interval_exprt(lower_bound, upper_bound);
      abstract_object_pointert meet_value =
        std::make_shared<interval_abstract_valuet>(meet_interval);
      if(meet_interval.is_single_value_interval())
        meet_value = std::make_shared<constant_abstract_valuet>(lower_bound);
      meet_values.insert(meet_value);
    }
  }

  if(meet_values.empty()) // no meet :(
    return std::make_shared<value_set_abstract_objectt>(type(), false, true);

  return resolve_values(meet_values);
}

abstract_object_pointert value_set_abstract_objectt::resolve_values(
  const abstract_object_sett &new_values) const
{
  PRECONDITION(!new_values.empty());

  if(new_values == values)
    return shared_from_this();

  auto unwrapped_values = unwrap_and_extract_values(new_values);

  if(unwrapped_values.size() > max_value_set_size)
  {
    return std::make_shared<interval_abstract_valuet>(
      unwrapped_values.to_interval());
  }

  auto result =
    std::dynamic_pointer_cast<value_set_abstract_objectt>(mutable_clone());
  result->set_values(unwrapped_values);
  return result;
}

void value_set_abstract_objectt::set_top_internal()
{
  values.clear();
  values.insert(std::make_shared<constant_abstract_valuet>(type()));
}

void value_set_abstract_objectt::set_values(
  const abstract_object_sett &other_values)
{
  PRECONDITION(!other_values.empty());
  if(are_any_top(other_values))
  {
    set_top();
  }
  else
  {
    set_not_top();
    values = other_values;
  }
  set_not_bottom();
  verify();
}

void value_set_abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_top())
  {
    out << "TOP";
  }
  else if(is_bottom())
  {
    out << "BOTTOM";
  }
  else
  {
    out << "value-set-begin: ";

    values.output(out, ai, ns);

    out << " :value-set-end";
  }
}

static abstract_object_sett
unwrap_and_extract_values(const abstract_object_sett &values)
{
  abstract_object_sett unwrapped_values;
  for(auto const &value : values)
  {
    unwrapped_values.insert(maybe_extract_single_value(value));
  }

  return unwrapped_values;
}

static abstract_object_pointert
maybe_extract_single_value(const abstract_object_pointert &maybe_singleton)
{
  auto const &value_as_set = std::dynamic_pointer_cast<const value_set_tag>(
    maybe_singleton->unwrap_context());
  if(value_as_set)
  {
    PRECONDITION(value_as_set->get_values().size() == 1);
    PRECONDITION(!std::dynamic_pointer_cast<const context_abstract_objectt>(
      value_as_set->get_values().first()));

    return value_as_set->get_values().first();
  }
  else
    return maybe_singleton;
}

static bool are_any_top(const abstract_object_sett &set)
{
  return std::find_if(
           set.begin(), set.end(), [](const abstract_object_pointert &value) {
             return value->is_top();
           }) != set.end();
}
