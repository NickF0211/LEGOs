import sys
import time
from os.path import dirname, join, abspath
project_root = abspath(join(dirname(__file__), '..'))
sys.path.append(project_root)
from pysmt.shortcuts import Int, TRUE, FALSE, String, Real

from Analyzer.proof_reader import check_and_minimize
from Analyzer.shortcut import AND, Constraints, EQ, Implication, NEQ, OR, add_constraint, clear, create_action, GE, \
    create_type, \
    exists, \
    exists_first, forall, \
    solve, \
    adder, \
    ite, \
    min, \
    max


# sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))

boolean = create_action("boolean", [("value", "bool")])
natural = create_action("natural", [("value", "nat")])
val = create_action("Val", [("val", "int")])

# add constraint which use ITE

# c0 = EQ(Int(0), ite(FALSE(), Int(0), Int(1)))  # works well

# c1 = exists(boolean, lambda d1: exists([natural, natural], lambda d2, d3: EQ(d2.value, ite(d1.value, d2.value, d3.value))))

c3 = exists(val, lambda v: AND(EQ(v.val, ite(exists(natural, lambda n: n.value > 5), Int(0), Int(1)) ), EQ(Int(0), v.val)))  # works well

# condition1 = exists(natural, lambda n: n.value < 20)
c6 = EQ(Int(1), ite(c3, Int(1), Int(2)))
# condition2 = exists(natural, lambda n: n.value > 5)
# condition3 = forall(natural, lambda n: n.value > 10)
# c7 = EQ(Int(1), ite(AND(condition2, condition1), Int(1), Int(0)))
# c8 = EQ(Int(1), ite(condition1, Int(1), Int(0)))
# c9 = EQ(Int(1), ite(condition3, Int(1), Int(0)))

# condition3 = exists(natural, lambda n: n.value > 15)
# c8 = EQ(Int(1), ite(AND(condition1, condition2, condition3), Int(1), Int(0)))

# c9 = EQ(ite(ite(TRUE(), TRUE(), FALSE()), Int(1), Int(0)), Int(1))
# for c9 should be true with empty domain
# works well for iff on not(condition_constraint) not good for invert
# iff does help but invert makes it worse


# c10 = EQ(TRUE(), ite(TRUE(), TRUE(), FALSE()))  # not working, prob change EQ
# c10 = exists(natural, lambda n: n.value > 300)
# c12 = forall(natural, lambda n: n.value > 4)
# c11 = EQ(Real(3.14), ite(FALSE(), Real(3.14), Real(2.71)))

print("going to add constraints")

add_constraint(c6)
add_constraint(c3)  
# add_constraint(c8)
# add_constraint(c9)
# add_constraint(c12)

# test time taken 
start = time.time()
solve(TRUE())
end = time.time()
print(end - start)


# assume value is anything
# assume value is natural number, first > second special case
# understand what to return, how to make sure value returned make sense(constraint) how to add those? which stage you want to enforce the constraint
# how to interact with other operators


# all the object pysmt can not recognize, try to create pysmt can understand, encode try to convert expression to pysmt can understand

# 1. arith operator functions , encode to pysmt: simple ite, ite with ite inside, with quantifiers outside, quantifiers depending on ite value

# type constructor under constraint line 361


# problem: self.var type def: clear ; embedded ite in ite: clear ; iteration constraint activate; eq, neq; optimal case
