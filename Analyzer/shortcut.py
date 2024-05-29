from pysmt.typing import INT, BOOL
import type_constructor
import logic_operator
import analyzer
from proof_reader import check_and_minimize
from pysmt.shortcuts import Int, Real, Bool, Symbol, TRUE, FALSE, FreshSymbol

type_dict = {}
CLASSES = []
Constraints = []


def create_type(name, upper_bound=None, lower_bound=None, var_type=INT, enum=None,
                customized_func=None):
    type_constructor.create_type(name, type_dict, upper_bound, lower_bound, var_type, enum, customized_func)


# default type
create_type("nat", lower_bound=0)
create_type("int")
create_type("time", lower_bound=0)
create_type("bool", var_type=BOOL)


def create_action(action_name, attributes):
    new_class = type_constructor.create_action(action_name, attributes, type_dict)
    CLASSES.append(new_class)
    return new_class


# logical connective
AND = logic_operator.AND
OR = logic_operator.OR
Implication = logic_operator.Implication
IFF = logic_operator.IFF
EQ = logic_operator.EQ
NEQ = logic_operator.NEQ
forall = logic_operator.forall
exists = logic_operator.exist
NOT = logic_operator.NOT
GT = logic_operator.GT
LT = logic_operator.LT
GE = logic_operator.GE
LE = logic_operator.LE


def add_constraint(constraint):
    Constraints.append(constraint)


# solver option
def solve(formulas, constraint_abstraction=False, vol_bound=500, solution_opt=False,
          proof_mode=False, unsat_mode=False):
    if not constraint_abstraction:
        rules = Constraints
    else:
        rules = []

    result = analyzer.check_property_refining(formulas, rules, Constraints,
                                              CLASSES, [], vol_bound=vol_bound,
                                              min_solution=solution_opt, record_proof=proof_mode,
                                              unsat_mode=unsat_mode)
    clear()
    analyzer.clear_rules([formulas])
    return result


def clear(reset_signature=False):
    analyzer.clear_all(CLASSES, Constraints)
    if reset_signature:
        CLASSES.clear()
        type_dict.clear()
        create_type("nat", lower_bound=0)
        create_type("int")
        create_type("time", lower_bound=0)
        create_type("bool", var_type=BOOL)


'''
Define the existence of a relational object of Class
that holds for the predicate  
and yields the greatest value according to the valuation function
'''


def exists_max(Class, predicate, valuation):
    return exists(Class, lambda o: AND(predicate(o),
                                       forall(Class, lambda o_prime, o=o:
                                       Implication(predicate(o_prime),
                                                   valuation(o) >= valuation(o_prime)))))


'''
Define the existence of a relational object of Class
that holds for the predicate  
and yields the smallest value according to the valuation function
'''


def exists_min(Class, predicate, valuation):
    return exists(Class, lambda o: AND(predicate(o),
                                       forall(Class, lambda o_prime, o=o:
                                       Implication(predicate(o_prime),
                                                   valuation(o) <= valuation(o_prime)))))


def exists_first(Class, predicate):
    return exists_min(Class, predicate, lambda o: o.time)


def exists_last(Class, predicate):
    return exists_max(Class, predicate, lambda o: o.time)
