import sys
from os.path import dirname, join

sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
from Analyzer.shortcut import *

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

# okay, let's take a look at a tree with height 3
solve(exists(Node, lambda n: n > Int(4)))


# for a given level, let's verify the maxiumn number of nodes for a given level i is <= 2^i

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


solve(check_node_number_at_i(3))
