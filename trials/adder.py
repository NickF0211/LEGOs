import sys
from os.path import dirname, join

from pysmt.shortcuts import Int, TRUE

from Analyzer.proof_reader import check_and_minimize
from Analyzer.shortcut import AND, Constraints, EQ, Implication, NEQ, OR, add_constraint, clear, create_action, \
    create_type, \
    exists, \
    exists_first, forall, \
    solve, \
    ADDER


sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))

Data = create_action("Data", [("value", "bool")])

add_constraint(exists(Data, lambda d: ADDER(d.value, d.value, d.value)))


solve(TRUE())
print("*"*100)
