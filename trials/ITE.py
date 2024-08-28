import sys
from os.path import dirname, join, abspath
project_root = abspath(join(dirname(__file__), '..'))
sys.path.append(project_root)
from pysmt.shortcuts import Int, TRUE, FALSE

from Analyzer.proof_reader import check_and_minimize
from Analyzer.shortcut import AND, Constraints, EQ, Implication, NEQ, OR, add_constraint, clear, create_action, \
    create_type, \
    exists, \
    exists_first, forall, \
    solve, \
    adder, \
    ite


# sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))

boolean = create_action("boolean", [("value", "bool")])
natural = create_action("natural", [("value", "nat")])
val = create_action("Val", [("val", "int")])

# add constraint which use ITE

c0 = EQ(Int(0), ite(TRUE(), Int(0), Int(1)))  # works well

c1 = exists(boolean, lambda d1: exists([natural, natural], lambda d2, d3: EQ(d2.value, ite(d1.value, d2.value, d3.value))))

c3 = exists(val, lambda v: AND(EQ(v.val, ite(exists(natural, lambda n: n.value > 5), Int(0), Int(1)) ), EQ(Int(0), v.val)))  # works well

# ITE structure: ITE(condition1, ITE(condition2, ITE(condition3, true_value1, false_value1), false_value2), false_value3)
condition1 = TRUE()
condition2 = FALSE()
condition3 = TRUE()
true_value1 = Int(7)
false_value1 = Int(3)
false_value2 = Int(8)
false_value3 = Int(12)

c4 = NEQ(Int(7), ite(condition1, ite(condition2, ite(condition3, true_value1, false_value1), false_value2), false_value3))

condition1 = exists(natural, lambda n: n.value > 5)
true_value_inner = ite(TRUE(), Int(1), Int(1))
false_value_outer = Int(5)

c5 = NEQ(Int(1), ite(condition1, true_value_inner, false_value_outer))

condition1 = exists(natural, lambda n: n.value < 5)
c6 = EQ(Int(1), ite(condition1, Int(1), Int(0)))

condition2 = exists(natural, lambda n: n.value > 10)
c7 = EQ(Int(1), ite(AND(condition1, condition2), Int(1), Int(0)))

condition3 = exists(natural, lambda n: n.value > 15)
c8 = EQ(Int(1), ite(AND(condition1, condition2, condition3), Int(1), Int(0)))

add_constraint(AND(c1, c4, c5))
solve(TRUE())


# assumer value is anything
# assume value is natural number, first > second special case
# understand what to return, how to make sure value returned make sense(constraint) how to add those? which stage you want to enforece the constraint
# how to interact with other operators


# all the object pysmt can not recognize, try to create pysmt can understand, encode try to convert expression to pysmt can understand

# 1. arith operator functions , encode to pysmt: simple ite, ite with ite inside, with quantifiers outside, quantifiers depending on ite value

# type constructor under constraint line 361


# problem: self.var type def: clear ; embedded ite in ite: clear ; iteration constraint activate; eq, neq; optimal case
