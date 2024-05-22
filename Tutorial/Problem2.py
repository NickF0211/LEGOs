from pysmt.typing import BOOL

import sys
sys.setrecursionlimit(1500)

from os.path import dirname, join
sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
from shortcut import *


FetherID = Int(0)
TarID = Int(1)

'''
Task 1, create your signautre here
'''
User = create_action("User",
                     [("id", "nat"),
                      ("bf", "nat"),
                      ("isDoctor", "bool"),
                      ("isPatient", "bool"),
                      ("sane", "bool"),
                      ("isPeculiar","bool"),
                      ("isSpecial","bool")])



'''
Task 2, define your rule here
'''
RULES = []

# 1. Tar is a docotor
Tar = User(input_subs={"presence": TRUE()})
add_constraint(AND(EQ(Tar.id, TarID), Tar.presence, Tar.isDoctor))

# 2. Fether is a doctor
Fether = User(input_subs={"presence": TRUE()})
add_constraint(AND(EQ(Fether.id, FetherID), Fether.presence, Fether.isDoctor))

#3 There are other doctors in the asylum.
C3 = exists(User, lambda u: AND(
    NEQ(u.id, Tar.id),
    NEQ(u.id, Fether.id),
    u.isDoctor
))

add_constraint(C3)

def believe(x, facts):
    return IFF(x.sane, facts)

#4 By definition, an inhabitant A is peculiar if A believes that A is a patient.
C4  = forall(User, lambda u: IFF(u.isPeculiar, believe(u, u.isPatient)))
add_constraint(C4)

#C5  By definition, an inhabitant A is special if all patients believe that A
# is peculiar and no doctor believes that A is peculiar
C5 = forall(User, lambda x: IFF(x.isSpecial,
                                        forall(User, lambda y:
                                               AND(Implication(y.isPatient, believe(y, x.isPeculiar)),
                                                   Implication(y.isDoctor, NOT(believe(y, x.isPeculiar))))
                                               )))

add_constraint(C5)

#C6 At least one inhabitant is sane.
C6 = exists(User, lambda u: u.sane)
add_constraint(C6)

#C7 Condition C: Given any two inhabitants, A and B, if A believes that B is special,
# then A’s best friend believes that B is a patient.
C7 = forall([User, User], lambda a, b: Implication(believe(a, b.isSpecial),
                                                   exists(User, lambda u: AND(EQ(u.id, a.bf),
                                                                             believe(u, b.isPatient)))
                                                   ))
add_constraint(C7)

#C8 Tarr believes that every doctor is sane.
C8 = believe(Tar, forall(User, lambda u: Implication(u.isDoctor, u.sane)))
add_constraint(C8)

#C9 Tarr believes that at least one patient is insane.
C9 = believe(Tar, exists(User, lambda u: AND(u.isPatient, NOT(u.sane))))
add_constraint(C9)

#C10 Fether believes that every patient is insane.
C10 = believe(Fether, forall(User, lambda u: Implication(u.isPatient, NOT(u.sane))))
add_constraint(C10)

#C11  Fether believes that at least one doctor is sane
C11 = believe(Fether, exists(User, lambda u: AND(u.isDoctor, u.sane)))
add_constraint(C11)

#C12 Fether believes that Tarr is sane.
C12 = believe(Fether, Tar.sane)
add_constraint(C12)

# unique_ID
unique_id_rule = forall([User, User],
                        lambda u1, u2: Implication(EQ(u1.id, u2.id),
                                                   EQ(u1, u2)))

add_constraint(unique_id_rule)


solve(TRUE(), proof_mode=True, unsat_mode=True)
UNSAT_core, _ = check_and_minimize("proof.txt", "simplified.txt")
print('*' * 100)
print("UNSAT CORE")
for i in UNSAT_core:
    print(str(i))