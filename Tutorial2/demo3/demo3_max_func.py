import sys
from os.path import dirname, join

sys.path.append(join(dirname(dirname(dirname(__file__))), "Analyzer"))
from shortcut import *

# this is the example for slides 48 in SRI-3
Data = create_action("Data", [("val", "int")])
Func = create_action("Func", [("input", "int"), ("output", "int")])

add_constraint(forall(Func, lambda f: exists ([Data, Data], lambda d1, d2:
                      AND(EQ(d1.val, f.input),
                          EQ(d2.val, f.output)))
                      ))

add_constraint(forall(Func, lambda f: f.output > f.input))

add_constraint(exists(Data, lambda d: forall(Func, lambda f: d.val > f.output)))

add_constraint(forall(Data, lambda d: exists(Func, lambda f: EQ(f.input, d.val))))

solve(TRUE(), proof_mode=True)
UNSAT, _ = check_and_minimize("proof.txt", "simple.txt")
for r in UNSAT:
    print(r)