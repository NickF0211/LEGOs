import sys
from os.path import dirname, join

from pysmt.shortcuts import Int, TRUE

from Analyzer.proof_reader import check_and_minimize
from Analyzer.shortcut import AND, Constraints, EQ, Implication, NEQ, OR, add_constraint, clear, create_action, \
    create_type, \
    exists, \
    exists_first, forall, \
    solve, \
    adder


sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))

Data = create_action("Data", [("value", "bool")])

# add_constraint(exists(Data, lambda d: exists(Data , lambda d2: AND(NEQ(d.value, d2.value), adder(d.value, d2.value, d2.value, d.value, d2.value)))))
# c1 = exists(Data, lambda d: EQ(d.value, TRUE()))
# c2 = forall(Data, lambda d: Implication(c1, EQ(d.value, TRUE())))
# # add constraint which use quantifiers in the ADDER
# add_constraint(forall(Data, lambda d: exists(Data, lambda d2: AND(NEQ(d.value, d2.value), adder(c1, d2.value, d2.value, d.value, d2.value)))))

add_constraint(adder(exists(Data, lambda d: EQ(d.value, TRUE())), TRUE(), TRUE(), TRUE(), TRUE()))

solve(TRUE())
print("*"*100)
