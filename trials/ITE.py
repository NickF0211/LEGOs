import sys
from os.path import dirname, join

from pysmt.shortcuts import Int, TRUE

from Analyzer.proof_reader import check_and_minimize
from Analyzer.shortcut import AND, Constraints, EQ, Implication, NEQ, OR, add_constraint, clear, create_action, \
    create_type, \
    exists, \
    exists_first, forall, \
    solve, \
    adder, \
    ITE


sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))

boolean = create_action("boolean", [("value", "bool")])
natural = create_action("natural", [("value", "nat")])

# add constraint which use ITE
c1 = exists(boolean, lambda d1: exists([natural, natural], lambda d2, d3: NEQ(d2.value, ITE(d1.value, d2.value, d3.value))))
add_constraint(c1)
solve(TRUE())
