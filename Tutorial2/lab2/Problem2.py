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
# User =



'''
Task 2, define your rule here
'''



# solve(TRUE())
solve(TRUE(), proof_mode=True, unsat_mode=True)
UNSAT_core, _ = check_and_minimize("proof.txt", "simplified.txt")
print('*' * 100)
print("UNSAT CORE")
for i in UNSAT_core:
    print(str(i))

'''
Task 4a: Put the UNSAT Core here.
'''


'''
Task 4b: The satisfying solution goes here. Explain why the solution violates the removed constraint 
'''

