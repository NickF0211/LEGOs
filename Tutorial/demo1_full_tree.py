import sys
from os.path import dirname, join

sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
from shortcut import *

create_type("id", lower_bound=1)
Node = create_action("Node",
                     [("id", "id"), ("parent", "nat"), ("time", "time")])  # here time is used to represent height

# 1 every non-root node has a valid parent
add_constraint(forall(Node, lambda n: Implication(n > Int(0),
                                                  exists(Node, lambda n_parent:
                                                  AND(EQ(n_parent.time, n.time - Int(1)),
                                                      EQ(n.parent, n_parent.id))
                                                         ))))

# 2 only node with id=1 is the root
add_constraint(exists(Node, lambda root: AND(EQ(root.id, Int(1)),
                                             EQ(root.parent, Int(0)))))

add_constraint(forall(Node, lambda n: Implication(n.id > Int(1),
                                                  n > Int(0))))

# 3, every node is unqiue with respect to id
add_constraint(forall([Node, Node], lambda n1, n2: Implication(EQ(n1.id, n2.id),
                                                               EQ(n1, n2))))

# 4 every node is either a leaf (whose height is the max) or has two children
add_constraint(forall(Node, lambda n: OR(
    AND(forall(Node, lambda child: NEQ(child.parent, n.id)),
        # forall(Node, lambda other: other <= n)
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

# Q1: let's take a look at a tree with height 3
print("A tree of height at least 3")
solve(exists(Node, lambda n: n >= Int(3)))

# let's define a path
Path = create_action("path", [("start", "id"), ("end", "id"), ("length", "nat")])

# let's define the constraint for a path:

# the length of a path must be consistent with the depth of the noddes
add_constraint(forall(Path, lambda p:
exists([Node, Node], lambda n1, n2:
AND(
    EQ(n1.id, p.start),
    EQ(n2.id, p.end),
    EQ(n2.time - n1.time, p.length)
)
       )))

# a path either is path to a node itself
add_constraint(forall(Path, lambda p: OR(
    AND(EQ(p.start, p.end), EQ(p.length, Int(0))),  # a node to itself is a path
    exists(Path, lambda p_next:
    exists([Node, Node], lambda n1, n2:
    AND(
        EQ(n1.id, p.start),
        EQ(n2.id, p_next.start),
        EQ(n2.parent, n1.id),
        EQ(p_next.end, p.end),
        EQ(p_next.length, p.length - 1)
    )
           )
           )
)))

# Q2 warm up:
# first let's see a path of length at least 3
print("A path of length at least 4")
solve(exists(Path, lambda p: p.length > 3))

# Q2:
# now let's define the constraint that assume the existence of a cycle
cycle_assumption = exists([Path, Path], lambda p1, p2:
AND(
    EQ(p1.start, p2.end),
    EQ(p2.start, p1.end),
    # EQ(p1.length, p2.length),
    p1.length > 0
)
                          )

# let's see try to look for a cycle
print("is there a cycle in a tree?")
solve(cycle_assumption, proof_mode=True)
UNSAT_Core, _ = check_and_minimize("proof.txt", "cycle_proof.txt")
for r in UNSAT_Core:
    print(r)


# Q3:
# for a given level, let's verify the maximum number of nodes for a given level i is <= 2^i
def _constraint_helper(remain, i, nodes):
    if remain == 0:
        cur_constraint = TRUE()
        if not nodes:
            return cur_constraint
        else:
            cur_node = nodes[0]
            for j in range(1, len(nodes)):
                new_cur_node = nodes[j]
                cur_constraint = AND(cur_constraint, new_cur_node.id > cur_node.id)
                cur_node = new_cur_node
            height_constraint = AND([EQ(n.time, Int(i)) for n in nodes])
        return AND(height_constraint, cur_constraint
                   )
    else:
        return exists(Node, lambda n, remain=remain, i=i, nodes=nodes:
        _constraint_helper(remain - 1, i, nodes + [n])
                      )


def check_node_number_at_i(i):
    n = (2 ** i) + 1
    constraints = _constraint_helper(n, i, [])
    return constraints


# now let's prove this claim for depth 2
print("prove the claim that the maximum number of nodes for a given level i is <= 2^i")
solve(check_node_number_at_i(2))
