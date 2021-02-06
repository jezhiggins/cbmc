/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::merge

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

static std::shared_ptr<value_set_abstract_objectt>
  make_value_set(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<value_set_abstract_objectt>(val, env, ns);
}

static std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<constant_abstract_valuet>(val, env, ns);
}

static std::shared_ptr<value_set_abstract_objectt>
make_value_set(const std::vector<exprt> &vals, abstract_environmentt &env, namespacet &ns)
{
  auto initial_values = abstract_object_sett { };
  for (auto v : vals)
    initial_values.insert(make_constant(v, env, ns));
  auto vs = make_value_set(vals[0], env, ns);
  vs->set_values(initial_values);
  return vs;
}

static std::shared_ptr<const value_set_abstract_objectt>
  as_value_set(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const value_set_abstract_objectt>(aop);
}

static bool
set_contains(const abstract_object_sett &set, const exprt val)
{
  auto i = std::find_if(set.begin(), set.end(),
    [&val](const abstract_object_pointert &lhs)
    {
      auto l = lhs->to_constant();
      return l == val;
    });
  return i != set.end();
}

SCENARIO(
  "merging two value_set_abstract_objects",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("Two value sets")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt { object_factory };
    environment.make_top();
    auto symbol_table = symbol_tablet { };
    auto ns = namespacet { symbol_table };

    WHEN("merging { 1 } with { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1 } is unchanged ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());
        REQUIRE(value_set_result->get_values().size() == 1);
        REQUIRE(value_set_result->to_constant() == val1);

        // Is optimal
        REQUIRE(result == op1);
      }
    }

    WHEN("merging { 1 } with { 2 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2 }")
      {
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());

        auto values = value_set_result->get_values();
        REQUIRE(values.size() == 2);

        REQUIRE(set_contains(values, val1));
        REQUIRE(set_contains(values, val2));
      }
    }

    WHEN("merging { 1, 2 } with { 2 }")
    {
      auto op1 = make_value_set({ val1, val2 }, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1, 2 } is unchanged")
      {
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());

        auto values = value_set_result->get_values();
        REQUIRE(values.size() == 2);

        REQUIRE(set_contains(values, val1));
        REQUIRE(set_contains(values, val2));
      }
    }

    WHEN("merging { 1, 2 } with { 3, 4 }")
    {
      auto op1 = make_value_set({ val1, val2 }, environment, ns);
      auto op2 = make_value_set({ val3, val4 }, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2, 3, 4 }")
      {
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());

        auto values = value_set_result->get_values();
        REQUIRE(values.size() == 4);

        REQUIRE(set_contains(values, val1));
        REQUIRE(set_contains(values, val2));
        REQUIRE(set_contains(values, val3));
        REQUIRE(set_contains(values, val4));
      }
    }

    WHEN("merging { 1, 2, 3 } with { 1, 3, 4 }")
    {
      auto op1 = make_value_set({ val1, val2, val3 }, environment, ns);
      auto op2 = make_value_set({ val1, val3, val4 }, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2, 3, 4 }")
      {
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());

        auto values = value_set_result->get_values();
        REQUIRE(values.size() == 4);

        REQUIRE(set_contains(values, val1));
        REQUIRE(set_contains(values, val2));
        REQUIRE(set_contains(values, val3));
        REQUIRE(set_contains(values, val4));
      }
    }
  }
}

SCENARIO(
  "merging a value_set with a constant",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("Two value sets")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1 } with 1")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1 } is unchanged ")
      {
        // Though we may become top or bottom, the type should be unchanged
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE_FALSE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());
        REQUIRE(value_set_result->get_values().size() == 1);
        REQUIRE(value_set_result->to_constant() == val1);

        // Is optimal
        REQUIRE(result == op1);
      }
    }

    WHEN("merging { 1 } with 2")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1, 2 }")
      {
        REQUIRE(value_set_result);

        // Correctness of merge
        REQUIRE(modified);
        REQUIRE_FALSE(value_set_result->is_top());
        REQUIRE_FALSE(value_set_result->is_bottom());

        auto values = value_set_result->get_values();
        REQUIRE(values.size() == 2);

        REQUIRE(set_contains(values, val1));
        REQUIRE(set_contains(values, val2));
      }
    }
  }
}