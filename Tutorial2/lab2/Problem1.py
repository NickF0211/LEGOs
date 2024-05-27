'''
Problem 1:

In this problem, we would like you to model a puzzle question in FOL*
and solve the puzzles with FOL* satisfiability result:
'''
import sys
from os.path import dirname, join

sys.path.append(join(dirname(dirname(dirname(__file__))), "Analyzer"))
from shortcut import *

Basics = [2, 3]
# Basics = [3, 5]

'''
Task 1: define the FOL* signature to capture the concept of constructed number
'''

'''
Solution 1:
'''
# create your custom action
#NUMBER =

'''
Task 2: encode FOL* constraint to capture the construction rules. You may assume the set `Basics` is given.
'''

'''
Solution 2:
'''




'''
Task 3:Suppose Basics = {2, 3} are given, try to find ways to construct the 
following target numbers: i = 1,  i =6 , i =17, i =28, i =45,  i =150, i =1501
Please call clear() after each call to LEGOs:
e.g., 
solve(property)
clear()
'''

'''
Solution 3:
'''


def check_target(target_value:int):
    pass


check_target(1)
check_target(6)
check_target(17)
check_target(28)
check_target(45)
check_target(150)
check_target(1501)

'''
Task 4: Suppose Basics = {3, 5} are given, try to find ways to construct the following target numbers: 
i = 14.  You might have noticed that the construction is impossible,
 but the tool cannot conclude UNSAT. Try to think about adding new FOL* class 
 and rules to help conclude UNSAT.
 
 Hint1: Adding three odd numbers always yields an odd number.  
 Therefore, if Basics contains only ODD numbers, then all Numbers constructed are ODD. 
 You can try to define two classes ODD and EVEN as abstractions off Number, 
 and define their construction rules respectively.
'''

Basics = [3, 5]

'''
Solution 4:
'''




def target_transformation(target:int):
    pass


def check_target_with_abstraction(target_value):
    target_property = target_transformation(target_value)
    solve(target_property, proof_mode=True)

check_target_with_abstraction(79)
check_target_with_abstraction(78)
check_target_with_abstraction(129)
check_target_with_abstraction(1100)
# we check the proof of UNSAT for 1100
UNSAT_core, _ = check_and_minimize("proof.txt", "simply.txt")
for r in UNSAT_core:
    print(r)

