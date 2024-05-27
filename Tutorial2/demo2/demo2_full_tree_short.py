import sys
from os.path import dirname, join


sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
from shortcut import *

'''
SRI-3: slides 6  Tree example.
'''


create_type("id", lower_bound=1)
Node = create_action("Node",
                     [("id", "id"), ("parent", "nat"), ("time", "time")])  # here time is used to represent height



add_constraint(forall(Node, lambda n: Implication(n > Int(0),
                                                  exists(Node, lambda n_parent:
                                                  AND(EQ(n_parent.time, n.time - Int(1)),
                                                      EQ(n.parent, n_parent.id))
                                                         ))))


add_constraint(exists(Node, lambda root: AND(EQ(root.id, Int(1)),
                                             EQ(root.parent, Int(0)))))

add_constraint(forall(Node, lambda n: Implication(n.id > Int(1),
                                                  n > Int(0))))

add_constraint(forall([Node, Node], lambda n1, n2: Implication(EQ(n1.id, n2.id),
                                                               EQ(n1, n2))))

add_constraint(forall(Node, lambda n: OR(
    AND(forall(Node, lambda child: NEQ(child.parent, n.id)),
        forall(Node, lambda other: other <= n)
        ),
    exists([Node, Node], lambda c1, c2:
    AND(
        NEQ(c1, c2),
        EQ(c1.parent, n.id),
        EQ(c2.parent, n.id),
        forall(Node, lambda other_child:
        Implication(AND(NEQ(c1.id, other_child.id),
                        NEQ(c2.id, other_child.id)),
                    NEQ(other_child.parent, n.id)
                    )
               )
    )
           )
)))

'''
let's take a look at a tree with height 3
Action: run this python file.

in the trace: time here is height
'''
# Q1: let's take a look at a tree with height 3
print("A tree of height at least 3")
solve(exists(Node, lambda n: n >= Int(3)))


'''
the tree satisfying all FOL* constraints, but it is not a full tree.
Let's argument the previous requirement to define a full tree.
every node is either a leaf （whose height is the the maximum  among all nodes) or has two children

Action: Uncomment the commented out line in the previous constraint as well as the following two lines. 
Run this python file
'''
# print("A full tree of height at least 3")
# solve(exists(Node, lambda n: n >= Int(3)))

'''
The exercise from slides 6-10 can be found in demo2_full_tree_long.py as well. Please 
take a look before the lab.
'''

