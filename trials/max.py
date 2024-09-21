import sys
import time
from os.path import dirname, join, abspath
project_root = abspath(join(dirname(__file__), '..'))
sys.path.append(project_root)
from pysmt.shortcuts import Int, TRUE, FALSE, String, Real

from Analyzer.proof_reader import check_and_minimize
from Analyzer.shortcut import AND, Constraints, EQ, GE, Implication, NEQ, OR, add_constraint, clear, create_action, \
    create_type, \
    exists, \
    exists_first, forall, \
    solve, \
    adder, \
    ite, \
    max, \
    min

natural = create_action("natural", [("val", "nat")])
# predicate = lambda x: GE(x.val, Int(0))
# func = lambda x: x.val + Int(1)
# checking_class = natural
# cond = exists(checking_class, lambda obj: AND(
#             predicate(obj),
#             forall(natural, lambda obj1: Implication(
#                 predicate(obj1),
#                 GE(func(obj), func(obj1))
#             ))
#         ))
print("--------define constraint c0--------")
c0 = EQ(min(natural, lambda x: GE(x.val, Int(0)), lambda x: x.val + Int(11), int), Int(10))
print("--------define constraint c1--------")
c1 = exists(natural, lambda x: EQ(x.val, Int(11)))

add_constraint(c0)
add_constraint(c1)
solve(TRUE())