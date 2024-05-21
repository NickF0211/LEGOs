'''
Problem 1:

In this problem, we would like you to model a puzzle question in FOL*
and solve the puzzles with FOL* satisfiability result:
'''
import sys
from os.path import dirname, join
sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
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
NUMBER = create_action("number", [("val", "nat"), ("time", "time")])

'''
Task 2: encode FOL* constraint to capture the construction rules. You may assume the set `Basics` is given.
'''

'''
Solution 2:
'''
def base_case(num: NUMBER):
    return OR([EQ(num.val, Int(base_item)) for base_item in Basics])

def recursive_case(num: NUMBER):
    return exists([NUMBER, NUMBER, NUMBER], lambda num1, num2, num3, num=num:
    AND([num > num1,
         num > num2,
         num > num3,
         EQ(num.val, (num1.val + num2.val - num3.val)),
         num1.val >= num2.val]))


add_rule = forall(NUMBER, lambda num: OR(base_case(num), recursive_case(num)))
add_constraint(add_rule)

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
def check_target(target_value):
    target_property = exists(NUMBER, lambda num, target_value = target_value:
                                EQ(num.val, Int(target_value)))
    solve(target_property)


check_target(1)
clear()


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

EVEN = create_action("Even", [("time", "time")])
ODD = create_action("ODD", [("time", "time")])

even_rules = forall(EVEN, lambda even: OR(
    OR([TRUE() for i in Basics if not (i % 2)]),
    exists(EVEN, lambda even_prev: even > even_prev)
))

odd_rules = forall(ODD, lambda even: OR(
    OR([TRUE() for i in Basics if (i % 2)]),
    exists(ODD, lambda even_prev: even > even_prev)
))

add_constraint(even_rules)
add_constraint(odd_rules)


def target_transformation(target):
    goal = exists(NUMBER, lambda add: EQ(Int(target), add.val))
    if not (target % 2):
        abstracted_goal = exists(EVEN, lambda even: forall(EVEN, lambda even_prime: even <= even_prime))
    else:
        abstracted_goal = exists(ODD, lambda even: forall(ODD, lambda even_prime: even <= even_prime))
    return AND(goal, abstracted_goal)




def check_target_with_abstraction(target_value):
    target_property = target_transformation(target_value)
    solve(target_property, proof_mode=True)


check_target_with_abstraction(79)
check_target_with_abstraction(78)
UNSAT_core, _ = check_and_minimize("proof.txt", "simply.txt")
for r in UNSAT_core:
    print(r)
check_target_with_abstraction(129)
