import ntpath
import os.path
import sys
import time
from os.path import join, dirname

from pysmt.fnode import FNode
from termcolor import colored
sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))


from analyzer import check_property_refining, clear_all
from proof_reader import check_and_minimize
from type_constructor import create_type, create_action, union
from sleecOp import WhenRule, happen_within, otherwise, unless, complie_measure, Concern, EventRelation, \
    MeasureRelation, Causation, Effect, UntilEMRelation, TimedEMRelation
from logic_operator import *
import derivation_rule
from proof_reader import Fact

from textx import metamodel_from_file, textx_isinstance

grammar_file = "sleec-gramar.tx"
mm = metamodel_from_file(grammar_file)
constants = {}

VOL_BOUND = 20


def isXinstance(obj, cls):
    return textx_isinstance(obj, mm[cls])


def read_model_file(file_path):
    with open(file_path, 'r') as file:
        return file.read()

    # Create a metamodel from the grammar file


def parse_event_def(event, type_dict):
    # DressingStarted = create_action("DressingStarted", [("time", "time")], type_dict)
    return create_action(event.name, [("time", "time")], type_dict)


def match_default_sleec_data_type(typename):
    if typename == "numeric":
        return "int"
    elif typename == "boolean":
        return "bool"
    else:
        return None


scalar_type = {}
scalar_mask = {}
registered_type = set()


def add_scale(scalePaarams):
    sps = scalePaarams.scaleParams
    for index in range(len(sps)):
        sp = sps[index]
        if sp.name in scalar_type:
            assert scalar_type[sp.name] == index
        scalar_type[sp.name] = index


def process_scalar(measure, type_dict):
    if measure.name not in registered_type:
        scalar = measure.type
        add_scale(measure.type)
        create_type(measure.name, type_dict, upper_bound=len(scalar.scaleParams) - 1, lower_bound=0)
        scalar_mask[measure.name] = [t.name for t in measure.type.scaleParams]
        registered_type.add(measure.name)

    return measure.name, measure.name


def parse_measure_def(measure, type_dict):
    if isXinstance(measure, "ScalarMeasure"):
        return process_scalar(measure, type_dict)
    else:
        return measure.name, match_default_sleec_data_type(measure.type)


def parse_constants(constant, constants):
    value = constant.value
    if value.value:
        cur_val = value.value
    else:
        cur_val = parse_constants(value.constant, constants)
    if constant.name not in constants:
        constants[constant.name] = cur_val
    return cur_val


def parse_definitions(defs):
    ACTION_Mapping = {}
    _measures = [("time", "time")]
    type_dict = dict()

    # create the default types
    create_type("time", type_dict, lower_bound=0)
    create_type("int", type_dict)
    create_type("bool", type_dict, var_type=BOOL)

    for d in defs:
        if isXinstance(d, "Event"):
            ACTION_Mapping[d.name] = parse_event_def(d, type_dict)
        if isXinstance(d, "Measure"):
            _measures.append(parse_measure_def(d, type_dict))
        if isXinstance(d, "Constant"):
            parse_constants(d, constants)

    # Now, we should create the measure class
    ACTION_Mapping["Measure"] = create_action("Measure", _measures, type_dict)
    complie_measure(ACTION_Mapping["Measure"])
    return ACTION_Mapping


def parse_rules(rb, Action_Mapping):
    rules = []
    for r in rb.rules:
        rules.append(parse_element(r, Action_Mapping))
    return rules


def parse_relations(relationBlock, Action_Mapping):
    relations = []
    for r in relationBlock.relations:
        relations.append(parse_element(r, Action_Mapping))
    return relations


def parse_concerns(rb, Action_Mapping):
    concerns = []
    for c in rb.concerns:
        concerns.append(parse_element(c, Action_Mapping))
    return concerns


def parse_purposes(rb, Action_Mapping):
    purposes = []
    for c in rb.purposes:
        purposes.append(parse_element(c, Action_Mapping))
    return purposes


def parse_element(node, Action_Mapping, head=None, measure=None, is_pos=True):
    if isinstance(node, int) or isinstance(node, str):
        return node
    if node is None:
        return node
    if node == []:
        return None
    if isXinstance(node, "Rule"):
        res = parse_rule(node, Action_Mapping, head, measure, is_concern=False)
    elif isXinstance(node, "Concern"):
        res = parse_concern(node, Action_Mapping, head, measure)
    elif isXinstance(node, "Purpose"):
        res = parse_concern(node, Action_Mapping, head, measure)
    elif isXinstance(node, "Trigger"):
        res = parse_trigger(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Event"):
        res = parse_event(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "ExtendedResponse"):
        res = parse_extended_response(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Response") or isXinstance(node, "InnerResponse"):
        res = parse_response(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Occ"):
        res = parse_occ(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "TimeLimit"):
        res = parse_timelimit(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Value"):
        res = parse_value(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Alternative"):
        res = parse_response(node.response, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "NumTerminal"):
        res = parse_numterminal(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "NumMeasure"):
        res = parse_num_measure(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "BoolMeasure"):
        res = parse_bool_measure(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "ScalarMeasure"):
        res = parse_scalar_measure(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "NumericalOp"):
        res = parse_num_op(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "BoolBinaryOp"):
        res = parse_bool_bin_op(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "NumBinOp"):
        res = parse_num_bin_op(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Defeater"):
        res = parse_defeater(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Negation"):
        res = parse_negation(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "ScalarBinaryOp"):
        res = parse_scalar_binary_op(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "ScalarTerminal"):
        res = parse_scalar_terminal(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "ScaleParam"):
        res = parse_scale_param(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "BoolTerminal"):
        res = parse_bool_terminal(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Constant"):
        res = parse_value(node.value, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "TimeValue"):
        res = parse_timevalue(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "ND"):
        res = parse_response(node.response, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "EventRel"):
        res = parse_event_relation(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "MeasureRel"):
        res = parse_measure_relation(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "MeasureInv"):
        res = parse_measure_inv(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Causation"):
        res = parse_causation(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Effect"):
        res = parse_effect(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "Forbid"):
        res = parse_forbid(node, Action_Mapping, head, measure, is_pos)
    elif isXinstance(node, "UntilEM"):
        res = parse_untilEM(node, Action_Mapping)
    elif isXinstance(node, "TimedEM"):
        res = parse_timedEM(node, Action_Mapping)
    elif isXinstance(node, "RelType"):
        res = parse_relType(node)
    elif isXinstance(node, "MRelType"):
        res = parse_relType(node)
    else:
        assert False

    return res


def parse_concern(node, Action_Mapping, head, measure):
    trigger = parse_element(node.trigger, Action_Mapping, head, measure)
    if node.condition is not None:
        condition = lambda h, m, node=node, Action_Mapping=Action_Mapping: \
            parse_element(node.condition, Action_Mapping, h, m)
    else:
        condition = None

    if node.response:
        response = lambda h, m, node=node, Action_Mapping=Action_Mapping: \
            parse_element(node.response, Action_Mapping, h, m)
    else:
        response = lambda h, m, node=node, Action_Mapping=Action_Mapping: \
            TRUE()

    if node.next is not None:
        next_concern = parse_concern(node.next, Action_Mapping, head, measure)
    else:
        next_concern = None

    return Concern(trigger, action=response, rule_condition=condition, reference=node, next=next_concern)


def parse_untilEM(node, Action_Mapping):
    start_trigger = parse_element(node.start_trigger, Action_Mapping)
    if node.end_trigger is not None:
        end_trigger = parse_element(node.end_trigger, Action_Mapping)
    else:
        end_trigger =None


    if node.start_condition is not None:
        start_condition = lambda h, m, node=node, Action_Mapping=Action_Mapping: \
            parse_element(node.start_condition, Action_Mapping, h, m)
    else:
        start_condition = None

    if node.end_condition is not None:
        end_condition = lambda h, m, node=node, Action_Mapping=Action_Mapping: \
            parse_element(node.end_condition, Action_Mapping, h, m)
    else:
        end_condition = None

    response = lambda m, node=node, Action_Mapping=Action_Mapping: \
        parse_element(node.inv, Action_Mapping, m, m, is_pos=True)

    return UntilEMRelation(start_trigger, end_trigger, start_condition, end_condition, response, node)


def parse_timedEM(node, Action_Mapping):
    start_trigger = parse_element(node.start_trigger, Action_Mapping)
    duration = lambda m, node=node, Action_Mapping=Action_Mapping: parse_element(node.duration, Action_Mapping, m, m)
    response = lambda m, node=node, Action_Mapping=Action_Mapping: \
        parse_element(node.inv, Action_Mapping, m, m, is_pos=True)

    return TimedEMRelation(start_trigger, duration, response, node)


def parse_rule(node, Action_Mapping, head, measure, is_concern=False, is_pos=True):
    trigger = parse_element(node.trigger, Action_Mapping, head, measure, is_pos)
    if node.condition is not None:
        condition = lambda h, m, node=node, Action_Mapping=Action_Mapping, is_pos=is_pos: \
            parse_element(node.condition, Action_Mapping, h, m, is_pos)
    else:
        condition = None

    if not is_concern or node.response:
        response = lambda h, m, node=node, Action_Mapping=Action_Mapping, is_pos=is_pos: \
            parse_element(node.response, Action_Mapping, h, m, is_pos=True)
        neg_response = lambda h, m, node=node, Action_Mapping=Action_Mapping, is_pos=is_pos: \
            parse_element(node.response, Action_Mapping, h, m, is_pos=False)
    else:
        neg_response = response = lambda h, m, node=node, Action_Mapping=Action_Mapping, is_pos=is_pos: \
            TRUE()

    if is_concern:
        return Concern(trigger, action=response, rule_condition=condition, reference=node)
    else:
        return WhenRule(trigger, action=response, neg_action=neg_response, rule_condition=condition, reference=node)


def parse_relType(node):
    if node == "witness":
        return Implication
    elif node == "conflict":
        return lambda a, b: NOT(AND(a, b))
    elif node == "coincide":
        return IFF
    elif node == "opposition":
        return lambda a, b: NOT(IFF(a, b))
    else:
        print("unsupport relation type")
        assert False


def parse_event_relation(node, Action_Mapping, head, measure, is_pos):
    rel_op = parse_element(node.rel, Action_Mapping, head, measure, is_pos)
    lhs = parse_element(node.lhs, Action_Mapping, head, measure, is_pos)
    rhs = parse_element(node.rhs, Action_Mapping, head, measure, is_pos)
    return EventRelation(rel_op, lhs, rhs, reference=node)


def process_op(op_str):
    if op_str == "imply":
        return Implication
    elif op_str == "mutualExclusive":
        return lambda a, b: Implication(a, NOT(b))
    elif op_str == "iff":
        return IFF
    elif op_str == "opposite":
        return lambda a, b: AND(Implication(a, NOT(b)), Implication(b, NOT(a)))
    else:
        print("unsupport relation type")
        assert False


def parse_measure_relation(node, Action_Mapping, head, measure, is_pos):
    rel_op = process_op(parse_element(node.rel, Action_Mapping, head, measure, is_pos))
    expr = lambda m, node=node, Action_Mapping=Action_Mapping, head=head, is_pos=is_pos, rel_op=rel_op: \
        rel_op(
            parse_element(node.lhs, Action_Mapping, head, m, is_pos),
            parse_element(node.rhs, Action_Mapping, head, m, is_pos))
    return MeasureRelation(expr, reference=node)


def parse_measure_inv(node, Action_Mapping, head, measure, is_pos):
    expr = lambda m, node=node, Action_Mapping=Action_Mapping, head=head, is_pos=is_pos: \
        parse_element(node.expr, Action_Mapping, head, m, is_pos)
    return MeasureRelation(expr, reference=node)


def parse_causation(node, Action_Mapping, head, measure, is_pos):
    cause = parse_element(node.cause, Action_Mapping, head, measure, is_pos)
    effect = lambda m, node=node, Action_Mapping=Action_Mapping, head=head, is_pos=is_pos: \
        parse_element(node.effect, Action_Mapping, head, m, is_pos)

    return Causation(cause, effect, node)


def parse_effect(node, Action_Mapping, head, measure, is_pos):
    cause = parse_element(node.cause, Action_Mapping, head, measure, is_pos)
    effect = lambda m, node=node, Action_Mapping=Action_Mapping, head=head, is_pos=is_pos: \
        parse_element(node.effect, Action_Mapping, head, m, is_pos)

    return Effect(cause, effect, node)

def parse_forbid(node, Action_Mapping, head, measure, is_pos):
    cause = parse_element(node.cause, Action_Mapping, head, measure, is_pos)
    effect = lambda m, node=node, Action_Mapping=Action_Mapping, head=head, is_pos=is_pos: \
        NOT(parse_element(node.effect, Action_Mapping, head, m, is_pos))

    return Effect(cause, effect, node)


def parse_scale_param(node, Action_Mapping, head, measure, is_pos):
    return scalar_type[node.name]


def parse_trigger(node, Action_Mapping, head, measure, is_pos):
    return parse_element(node.event, Action_Mapping, head, measure, is_pos)


def parse_event(node, Action_Mapping, head, measure, is_pos):
    return Action_Mapping[node.name]


def parse_violation(node, Action_Mapping, current, violation, is_pos):
    assert isXinstance(node, "Occ")
    negation = node.neg
    event = parse_element(node.event, Action_Mapping, current, current, is_pos)
    if node.limit:
        start, end = parse_element(node.limit, Action_Mapping, current, current, is_pos)
    else:
        start = end = 0

    if not node.limit:
        if node.inf:
            start = end = -1
        else:
            start = end = 0

    if negation:
        return exist(Action_Mapping[event], lambda e, event=event: AND(EQ(e.time, violation.time),
                                                                       e.time <= current.time + end,
                                                                       e.time >= current.time,
                                                                       NOT(exist(Action_Mapping[event], lambda e_prime:
                                                                       AND(Not(e_prime < e.time),
                                                                           e_prime.time >= current.time))
                                                                           )))
    else:
        return EQ(current.time + end, violation.time)


def timed_occ(node):
    return node.limit is not None


def parse_extended_response(node, Action_Mapping, head, measure, is_pos):
    first = parse_element(node.head, Action_Mapping, head, measure, is_pos)
    if node.next is not None:
        second = parse_element(node.next, Action_Mapping, head, measure, is_pos)
        return AND(first, second)
    else:
        return first


def parse_response(node, Action_Mapping, head, measure, is_pos):
    occ = parse_element(node.occ, Action_Mapping, head, measure, is_pos)
    # alt = exist(Action_Mapping["Measure"], lambda m: AND(parse_violation(node, Action_Mapping, measure),
    #                                                      parse_element(node.alternative, Action_Mapping, m, m)))
    if node.alternative:
        if timed_occ(node.occ):
            if is_pos:
                alt = exist(Action_Mapping["Measure"], lambda violation_m, node=node, measure=measure, is_pos=is_pos:
                AND(
                    parse_violation(node.occ, Action_Mapping, measure, violation_m, is_pos),
                    parse_element(node.alternative, Action_Mapping,
                                  violation_m, violation_m, is_pos)))
            else:
                alt = forall(Action_Mapping["Measure"], lambda violation_m, node=node, measure=measure, is_pos=is_pos:
                Implication(
                    parse_violation(node.occ, Action_Mapping, measure, violation_m, is_pos),
                    parse_element(node.alternative, Action_Mapping,
                                  violation_m, violation_m, is_pos)))
        else:
            alt = parse_element(node.alternative, Action_Mapping, head, measure, is_pos)
    else:
        alt = None

    defeaters = [parse_element(defeater, Action_Mapping, head, measure, is_pos) for defeater in node.defeater]
    if alt:
        main_action = otherwise(TRUE(), occ, alt)
    else:
        main_action = occ

    if node.nd is not None:
        main_action = OR(main_action, parse_element(node.nd, Action_Mapping, head, measure, is_pos))

    if not defeaters:
        return main_action
    else:
        return unless([(TRUE(), main_action)] + defeaters, reference=node)


def parse_occ(node, Action_Mapping, head, measure, is_pos):
    negation = node.neg
    event = parse_element(node.event, Action_Mapping, head, measure, is_pos)
    if node.limit:
        start, end = parse_element(node.limit, Action_Mapping, head, measure, is_pos)
    else:
        start = end = 0

    if not node.limit:
        if node.inf:
            start = end = -1
        else:
            start = end = 0
    res = happen_within(event, head, start, end, ref=node)
    if negation:
        return NOT(res)
    else:
        return res


def parse_timevalue(node, Action_Mapping, head, measure, is_pos):
    if node.unit == "seconds":
        mul = 1
    elif node.unit == "minutes":
        mul = 60
    elif node.unit == "hours":
        mul = 3600
    elif node.unit == "days":
        mul = 3600 * 24
    else:
        print("invalid time unit")
        assert False
    return mul * parse_element(node.value, Action_Mapping, head, measure, is_pos)


def parse_timelimit(node, Action_Mapping, head, measure, is_pos):
    if node.start:
        start = parse_element(node.start, Action_Mapping, head, measure, is_pos)
    else:
        start = 0

    if node.end:
        end = parse_element(node.end, Action_Mapping, head, measure, is_pos)
    else:
        end = 0
    return start, end


def parse_value(node, Action_Mapping, head, measure, is_pos):
    if node.value is not None:
        return node.value
    else:
        return constants[node.constant]


def parse_numterminal(node, Action_Mapping, head, measure, is_pos):
    if node.value is not None:
        return parse_element(node.value, Action_Mapping, head, measure, is_pos)
    else:
        return parse_element(node.ID, Action_Mapping, head, measure, is_pos)


def parse_scalar_terminal(node, Action_Mapping, head, measure, is_pos):
    if node.value is not None:
        return parse_element(node.value, Action_Mapping, head, measure, is_pos)
    else:
        return parse_element(node.ID, Action_Mapping, head, measure, is_pos)


def parse_bool_terminal(node, Action_Mapping, head, measure, is_pos):
    if node.value is not None:
        res = parse_element(node.value, Action_Mapping, head, measure, is_pos)
    else:
        res = parse_element(node.ID, Action_Mapping, head, measure, is_pos)

    if isinstance(res, FNode):
        res = Bool_Terminal(res)
        text_ref[res] = node

    return res


def parse_num_measure(node, Action_Mapping, head, measure, is_pos):
    return getattr(measure, node.name)


def parse_bool_measure(node, Action_Mapping, head, measure, is_pos):
    return getattr(measure, node.name)


def parse_scalar_measure(node, Action_Mapping, head, measure, is_pos):
    return getattr(measure, node.name)


def parse_num_op(node, Action_Mapping, head, measure, is_pos):
    lhs = parse_element(node.lhs, Action_Mapping, head, measure, is_pos)
    rhs = parse_element(node.rhs, Action_Mapping, head, measure, is_pos)
    func = op_str_sleec(node.op)
    res = func(lhs, rhs)
    if isinstance(res, FNode):
        res = Bool_Terminal(res)
        text_ref[res] = node
    return res


def parse_scalar_binary_op(node, Action_Mapping, head, measure, is_pos):
    lhs = parse_element(node.lhs, Action_Mapping, head, measure, is_pos)
    rhs = parse_element(node.rhs, Action_Mapping, head, measure, is_pos)
    func = op_str_sleec(node.op)
    res = func(lhs, rhs)
    if isinstance(res, FNode):
        res = Bool_Terminal(res)
        text_ref[res] = node
    return res


def parse_bool_bin_op(node, Action_Mapping, head, measure, is_pos):
    lhs = parse_element(node.lhs, Action_Mapping, head, measure, is_pos)
    rhs = parse_element(node.rhs, Action_Mapping, head, measure, is_pos)
    if node.op == "and":
        return AND(lhs, rhs)
    elif node.op == "or":
        return OR(lhs, rhs)
    else:
        assert False


def parse_num_bin_op(node, Action_Mapping, head, measure, is_pos):
    lhs = parse_element(node.lhs, Action_Mapping, head, measure, is_pos)
    rhs = parse_element(node.rhs, Action_Mapping, head, measure, is_pos)
    func = op_str_sleec(node.op)
    return func(lhs, rhs)


def parse_defeater(node, Action_Mapping, head, measure, is_pos):
    expr = parse_element(node.expr, Action_Mapping, head, measure, is_pos)
    response = parse_element(node.response, Action_Mapping, head, measure, is_pos)
    if response is None:
        return (expr, TRUE())
    else:
        return (expr, response)


def parse_negation(node, Action_Mapping, head, measure, is_pos):
    return NOT(parse_element(node.expr, Action_Mapping, head, measure, is_pos))


def check_concerns(filename, mode, model, rules, concerns, relations, Action_Mapping, Actions, model_str="", to_print=True,
                   multi_entry=False):
    dir, name = ntpath.split((filename))
    path = "{}/{}/{}/{}".format(os.getcwd(),dir, name, mode).replace(".sleec", "")    
    if not os.path.isdir(path):
        os.makedirs(path)
    Measure = Action_Mapping["Measure"]
    first_inv = [Implication(exist(E, lambda _: TRUE()),
                             AND(
                                 exist(E, lambda e_first, E=E: forall(E, lambda e, e_f=e_first:
                                 e.time >= e_f.time
                                                                      ), should_include_action=class_non_empty(E)),
                                 exist(E, lambda e_last, E=E: forall(E, lambda e, e_l=e_last:
                                 e.time <= e_l.time
                                                                     ), should_include_action=class_non_empty(E)),
                             )) for E in Actions if E != Measure]

    measure_inv = forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2)))
    output = ""
    adj_hl = []
    concern_raised = False
    relations_constraint = get_relational_constraints(relations)
    csv_file = open("z3.csv", 'a')
    for i in range(len(concerns)):
        if to_print:
            print("check concern_{}".format(i + 1))
        else:
            output += "check concern_{}\n".format(i + 1)

        concern = concerns[i]
        start_time = time.time()
        res = check_property_refining(concern.get_concern(), set(first_inv), [r.get_rule() for r in rules] +
                                      relations_constraint + [measure_inv],
                                      Actions, [], True,
                                      min_solution=False,
                                      final_min_solution=True, restart=False, boundary_case=False,
                                      universal_blocking=False, vol_bound=VOL_BOUND, scalar_mask=scalar_mask
                                      )
        end_time = time.time()
        duration = end_time - start_time
        print("concern case {} solving time {}".format(i, duration))

        if res == 2:
            concern.get_concern().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()
            res = check_property_refining(concern.get_concern(), set(first_inv),
                                          [r.get_rule() for r in rules] + relations_constraint +
                                          [measure_inv] +
                                          first_inv,
                                          Actions, [], True,
                                          min_solution=False,
                                          final_min_solution=True, restart=False, boundary_case=False,
                                          universal_blocking=False, vol_bound=VOL_BOUND * 5,
                                          record_proof=False)

        if isinstance(res, str):
            concern_raised = True
            sat_result = "sat"
            if to_print:
                print("Concern is raised")

            concern_node = model.concernBlock.concerns[i]
            start, end = concern_node._tx_position, concern_node._tx_position_end
            output += "{}\n".format(model_str[start: end])
            output += "Concern is raised\n"
            output += res
            output += ("-" * 100 + '\n')
        elif res == -1:
            if to_print:
                print("Likely not raised")
            else:
                output += "Likely not raised\n"

        else:
            sat_result = "unsat"
            print("concern not raised")
        csv_file.write("{},{},{},{},{}\n".format(filename, mode, i,  sat_result, duration))
        clear_relational_constraints(relations)
        clear_all(Actions)
        reset_rules(rules)
        clear_relational_constraints(relations_constraint)
        [r.clear() for r in first_inv]
        measure_inv.clear()
        derivation_rule.reset()
        print("*" * 100)
        output += "*" * 100 + '\n'
    csv_file.close()
    return concern_raised, output, adj_hl


def check_conflict(filename, mode, model, rules, relations, Action_Mapping, Actions, model_str="", check_proof=False, to_print=True,
                   multi_entry=False, profiling=True):

    dir, name = ntpath.split((filename))
    path = "{}/{}/{}/{}".format(os.getcwd(),dir, name, mode).replace(".sleec", "")    
    if not os.path.isdir(path):
        os.makedirs(path)
    Measure = Action_Mapping["Measure"]

    if profiling:
        profiling_file = open("profiling_conflict.csv", 'w')
        profiling_file.write("raw_finish_time, proof_generation_time, proof_checking_time, raw_proof_size, raw_derivation_steps, trimmed_proof_size, trimmed_derivation_steps\n")

    first_inv = [Implication(exist(E, lambda _: TRUE()),
                             AND(
                                 exist(E, lambda e_first, E=E: forall(E, lambda e, e_f=e_first:
                                 e.time >= e_f.time
                                                                      ), should_include_action=class_non_empty(E)),
                                 exist(E, lambda e_last, E=E: forall(E, lambda e, e_l=e_last:
                                 e.time <= e_l.time
                                                                     ), should_include_action=class_non_empty(E)),
                             )) for E in Actions if E != Measure]

    measure_inv = forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2)))
    output = ""
    adj_hl = []
    conflict_res = False
    conflicting_set = set()
    relations_constraint = get_relational_constraints(relations)
    multi_output = []
    csv_file = open("z3.csv", 'a')
    for i in range(len(rules)):

        if multi_entry:
            output = ""
            adj_hl = []

        if to_print:
            print("check rule_{}".format(i + 1))
        else:
            output += "check rule_{}\n".format(i + 1)

        if i in conflicting_set and len(conflicting_set) <= 2:
            # if we have determined that i is in conflict with others:
            output += "Conflicting SLEEC rule:\n"
            target = model.ruleBlock.rules[i]
            start, end = target._tx_position, target._tx_position_end
            output += "{}\n".format(model_str[start: end])
            output += "Since it was mentioned in other conflict reported above:\n"
            output += "*" * 100 + '\n'
            continue
        rule = rules[i]

        if profiling:
            # we want to measure the raw analysis time
            raw_start_time = time.time()
            res = check_property_refining(rule.get_premise(), set(),
                                          [r.get_rule() for r in rules] + relations_constraint + [measure_inv],
                                          Actions, [], True,
                                          min_solution=False,
                                          final_min_solution=True, restart=False, boundary_case=False,
                                          universal_blocking=False, vol_bound=VOL_BOUND,
                                          record_proof=check_proof)
            raw_finish_time = time.time() - raw_start_time
            rule.get_premise().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()


        if profiling:
            proof_generation_start_time = time.time()
        res = check_property_refining(rule.get_premise(), set(first_inv),
                                      [r.get_rule() for r in rules] + relations_constraint + [measure_inv],
                                      Actions, [], True,
                                      min_solution=False,
                                      final_min_solution=True, restart=False, boundary_case=False,
                                      universal_blocking=False, vol_bound=VOL_BOUND * 5,
                                      record_proof=check_proof)

        if profiling:
            proof_generation_time = time.time() - proof_generation_start_time

        if res == 2:
            rule.get_premise().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()

            if profiling:
                proof_generation_start_time = time.time()

            res = check_property_refining(rule.get_premise(), set(first_inv),
                                          [r.get_rule() for r in rules] + relations_constraint +
                                          [measure_inv] +
                                          first_inv,
                                          Actions, [], True,
                                          min_solution=False,
                                          final_min_solution=True, restart=False, boundary_case=False,
                                          universal_blocking=False, vol_bound=VOL_BOUND,
                                          record_proof=check_proof)

            if profiling:
                proof_generation_time = time.time() - proof_generation_start_time

        if isinstance(res, str):
            sat_result = "sat"
            if to_print:
                print("Not Conflicting")
            else:
                output += "Not Conflicting\n"

        elif res == -1:
            if to_print:
                print("Likely Conflicting")
            else:
                output += "Likely Conflicting\n"

        else:
            sat_result = "unsat"
            conflict_res = True

        if profiling:
            proof_checking_time = 0
            raw_proof_size = 0
            raw_derivation_steps = 0
            trimmed_proof_size = 0
            trimmed_derivation_steps = 0

        if res == 0 and check_proof:
            if profiling:
                raw_proof_size = os.path.getsize("proof.txt")
                raw_derivation_steps = sum(1 for _ in open("proof.txt"))
            if profiling:
                proof_checking_start_time = time.time()

            result = check_and_minimize("proof.txt", "simplified.txt")

            if profiling:
                proof_checking_time = time.time() - proof_checking_start_time

            if profiling:
                trimmed_proof_size = os.path.getsize("simplified.txt")
                trimmed_derivation_steps = sum(1 for _ in open("simplified.txt"))

            if not result:
                print("warning Redundency info is not available")
                output += ("-" * 100 + '\n')
                clear_all(Actions)
                reset_rules(rules)
                measure_inv.clear()
                derivation_rule.reset()
                clear_relational_constraints(relations)
                [r.clear() for r in first_inv]
                continue
            UNSAT_CORE, derivation = result

            # print("*" * 100)
            print("UNSAT CORE")
            reasons = []
            for r in UNSAT_CORE:
                id = r.id
                if id == 0:
                    adjust_index = i
                    conflicting_set.add(adjust_index)
                    rule_model = model.ruleBlock.rules[adjust_index]
                elif id > len(rules):
                    if model.relBlock and id - 1 < len(model.relBlock.relations) + len(rules):
                        adjust_index = id - 1
                        rule_model = model.relBlock.relations[id - 1 - len(rules)]
                    else:
                        continue
                else:
                    adjust_index = id - 1
                    conflicting_set.add(adjust_index)
                    rule_model = model.ruleBlock.rules[adjust_index]

                # start, end = rule_model._tx_position, rule_model._tx_position_end
                if adjust_index == i:
                    target = rule_model
                    # print("Redundant SLEEC rule:")
                    # print(model_str[start: end])
                    # print("-" * 100)
                else:
                    reasons.append(rule_model)
                    # reasons += (model_str[start: end]) + '\n' + "-" * 100 + '\n'

            local_index = {}

            start, end = target._tx_position, target._tx_position_end
            output += "Conflicting SLEEC rule:\n"
            new_start = len(output)
            local_index[(start, end)] = new_start
            output += "{}\n".format(model_str[start: end])
            output += ("-" * 100 + '\n')
            output += ("-" * 100 + '\n')
            output += "Because of the following SLEEC rule:\n"
            output += ("-" * 100 + '\n')
            for r in reasons:
                start, end = r._tx_position, r._tx_position_end
                new_start = len(output)
                local_index[(start, end)] = new_start
                output += "{}\n".format(model_str[start: end])
                output += ("-" * 100 + '\n')

            print(output)

            print("TO BE HIGHLIGHTED")
            hls = get_high_light(derivation)
            for s, e in hls:
                s, e = find_relative_pos(s, e, local_index)
                adj_hl.append((s, e))
                print("{} : [{}, {}]".format(output[s: e], s, e))

            if multi_entry:
                multi_output.append((output, adj_hl))

        if profiling:
            print("sat_result: {}".format(sat_result))
            print("proof_generation_time: {}".format(proof_generation_time))
            csv_file.write("{},{},{},{},{}\n".format(filename, mode, i,  sat_result, proof_generation_time))
            profiling_file.write("{}, {}, {}, {}, {}, {}, {}\n".format(raw_finish_time, proof_generation_time,
                                                                     proof_checking_time, raw_proof_size, raw_derivation_steps,
                                                                     trimmed_proof_size, trimmed_derivation_steps))
        clear_all(Actions)
        reset_rules(rules)
        measure_inv.clear()
        derivation_rule.reset()
        clear_relational_constraints(relations)
        [r.clear() for r in first_inv]
        print("*" * 100)
        output += "*" * 100 + '\n'
    csv_file.close()
    if multi_entry:
        return multi_output
    else:
        return conflict_res, output, adj_hl


def check_purposes(model, purposes, rules, relations, Action_Mapping, Actions, model_str="", check_proof=False,
                   to_print=True,
                   multi_entry=False, profiling= True):
    Measure = Action_Mapping["Measure"]
    first_inv = [Implication(exist(E, lambda _: TRUE()),
                             AND(
                                 exist(E, lambda e_first, E=E: forall(E, lambda e, e_f=e_first:
                                 e.time >= e_f.time
                                                                      ), should_include_action=class_non_empty(E)),
                                 exist(E, lambda e_last, E=E: forall(E, lambda e, e_l=e_last:
                                 e.time <= e_l.time
                                                                     ), should_include_action=class_non_empty(E)),
                             )) for E in Actions if E != Measure]

    measure_inv = forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2)))
    output = ""
    adj_hl = []
    conflict_res = False
    conflicting_set = set()
    relations_constraint = get_relational_constraints(relations)
    multi_output = []

    if profiling:
        profiling_file = open("profiling_purpose.csv", 'w')
        profiling_file.write(
            "raw_finish_time, proof_generation_time, proof_checking_time, raw_proof_size, raw_derivation_steps, trimmed_proof_size, trimmed_derivation_steps\n")

    for i in range(len(purposes)):

        if multi_entry:
            output = ""
            adj_hl = []

        if to_print:
            print("check rule_{}".format(i + 1))
        else:
            output += "check rule_{}\n".format(i + 1)

        # if i in conflicting_set:
        #     # if we have determined that i is in conflict with others:
        #     output += "Conflicting SLEEC rule:\n"
        #     target = model.ruleBlock.rules[i]
        #     start, end = target._tx_position, target._tx_position_end
        #     output += "{}\n".format(model_str[start: end])
        #     output += "Since it was mentioned in other conflict reported above:\n"
        #     output += "*" * 100 + '\n'
        #     continue

        purpose = purposes[i]

        if profiling:
            # we want to measure the raw analysis time
            raw_start_time = time.time()
            check_property_refining(purpose.get_concern(), set(), [r.get_rule() for r in rules] +
                                    relations_constraint +
                                    [measure_inv],
                                    Actions, [], True,
                                    min_solution=False,
                                    final_min_solution=True, restart=False, boundary_case=False,
                                    universal_blocking=False, vol_bound=VOL_BOUND,
                                    record_proof=False,
                                    scalar_mask=scalar_mask)

            raw_finish_time = time.time() - raw_start_time
            purpose.get_concern().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()
        if profiling:
            proof_generation_start_time = time.time()

        res = check_property_refining(purpose.get_concern(), set(), [r.get_rule() for r in rules] +
                                      relations_constraint +
                                      [measure_inv],
                                      Actions, [], True,
                                      min_solution=False,
                                      final_min_solution=True, restart=False, boundary_case=False,
                                      universal_blocking=False, vol_bound=VOL_BOUND,
                                      record_proof=check_proof,
                                      scalar_mask=scalar_mask)

        if profiling:
            proof_generation_time = time.time() - proof_generation_start_time

        if res == 2:
            purpose.get_concern().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()

            if profiling:
                proof_generation_start_time = time.time()

            res = check_property_refining(purpose.get_concern(), set(first_inv),
                                          [r.get_rule() for r in rules]  + relations_constraint +
                                          [measure_inv] +
                                          first_inv,
                                          Actions, [], True,
                                          min_solution=False,
                                          final_min_solution=True, restart=False, boundary_case=False,
                                          universal_blocking=False, vol_bound=VOL_BOUND * 5,
                                          record_proof=check_proof)

            if profiling:
                proof_generation_time = time.time() - proof_generation_start_time

        if isinstance(res, str):
            if to_print:
                print("Not Blocking")
            else:
                output += "Not Blocking\n"

        elif res == -1:
            if to_print:
                print("Likely  blocking")
            else:
                output += "Likely  blocking\n"

        else:
            conflict_res = True

        if profiling:
            proof_checking_time = 0
            raw_proof_size = 0
            raw_derivation_steps = 0
            trimmed_proof_size = 0
            trimmed_derivation_steps = 0

        if res == 0 and check_proof:
            if profiling:
                raw_proof_size = os.path.getsize("proof.txt")
                raw_derivation_steps = sum(1 for _ in open("proof.txt"))

            if profiling:
                proof_checking_start_time = time.time()

            UNSAT_CORE, derivation = check_and_minimize("proof.txt", "simplified.txt")

            if profiling:
                proof_checking_time = time.time() - proof_checking_start_time

            if profiling:
                trimmed_proof_size = os.path.getsize("simplified.txt")
                trimmed_derivation_steps = sum(1 for _ in open("simplified.txt"))

            # print("*" * 100)
            print("UNSAT CORE")
            reasons = []
            for r in UNSAT_CORE:

                id = r.id
                if id == 0:
                    adjust_index = i
                    conflicting_set.add(adjust_index)
                    rule_model = model.ruleBlock.rules[adjust_index]
                elif id > len(rules):
                    if model.relBlock and id - 1 < len(model.relBlock.relations) + len(rules):
                        adjust_index = id - 1
                        rule_model = model.relBlock.relations[id - 1 - len(rules)]
                    else:
                        continue
                else:
                    adjust_index = id - 1
                    conflicting_set.add(adjust_index)
                    rule_model = model.ruleBlock.rules[adjust_index]

                # id = r.id
                # if id == 0:
                #     adjust_index = i
                # elif id > len(rules):
                #     continue
                # else:
                #     adjust_index = id - 1
                #
                # conflicting_set.add(adjust_index)

                # rule_model = model.ruleBlock.rules[adjust_index]
                purpose_model = model.purposeBlock.purposes[i]

                # start, end = rule_model._tx_position, rule_model._tx_position_end
                if id == 0:
                    target = purpose_model
                    # print("Redundant SLEEC rule:")
                    # print(model_str[start: end])
                    # print("-" * 100)
                else:
                    reasons.append(rule_model)
                    # reasons += (model_str[start: end]) + '\n' + "-" * 100 + '\n'

            local_index = {}

            start, end = target._tx_position, target._tx_position_end
            output += "Blocked SLEEC purpose:\n"
            new_start = len(output)
            local_index[(start, end)] = new_start
            output += "{}\n".format(model_str[start: end])
            output += ("-" * 100 + '\n')
            output += ("-" * 100 + '\n')
            output += "Because of the following SLEEC rule:\n"
            output += ("-" * 100 + '\n')
            for r in reasons:
                start, end = r._tx_position, r._tx_position_end
                new_start = len(output)
                local_index[(start, end)] = new_start
                output += "{}\n".format(model_str[start: end])
                output += ("-" * 100 + '\n')

            print(output)

            print("TO BE HIGHLIGHTED")
            hls = get_high_light(derivation)
            for s, e in hls:
                s, e = find_relative_pos(s, e, local_index)
                adj_hl.append((s, e))
                print("{} : [{}, {}]".format(output[s: e], s, e))

            if multi_entry:
                multi_output.append((output, adj_hl))

        if profiling:
            profiling_file.write("{}, {}, {}, {}, {}, {}, {}\n".format(raw_finish_time, proof_generation_time,
                                                                     proof_checking_time, raw_proof_size, raw_derivation_steps,
                                                                     trimmed_proof_size, trimmed_derivation_steps))


        clear_relational_constraints(relations)
        clear_all(Actions)
        reset_rules(rules)
        [r.clear() for r in first_inv]
        measure_inv.clear()
        derivation_rule.reset()
        print("*" * 100)
        output += "*" * 100 + '\n'

    if profiling:
        profiling_file.close()

    if multi_entry:
        return multi_output
    else:
        return conflict_res, output, adj_hl


def get_relational_constraints(relations):
    constraints = []
    for r in relations:
        constraints.append(r.encode())

    return constraints


def clear_relational_constraints(relations):
    for r in relations:
        r.clear()


def get_measure_inv(Measure, Actions):
    pure_actions = [act for act in Actions if act != Measure]
    return AND(forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2))),
               forall(union(pure_actions), lambda act: exist(Measure, lambda m: EQ(m.time, act.time))))


def check_red(filename, mode, model, rules, relations, Action_Mapping, Actions, model_str="", check_proof=False, to_print=True,
              multi_entry=False, profiling=False):
    dir, name = ntpath.split((filename))
    path = "{}/{}/{}/{}".format(os.getcwd(),dir, name, mode).replace(".sleec", "")    
    if not os.path.isdir(path):
        os.makedirs(path)
    Measure = Action_Mapping["Measure"]
    measure_inv = forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2)))
    first_inv = [Implication(exist(E, lambda _: TRUE()),
                             AND(
                                 exist(E, lambda e_first, E=E: forall(E, lambda e, e_f=e_first:
                                 e.time >= e_f.time
                                                                      ), should_include_action=class_non_empty(E)),
                                 exist(E, lambda e_last, E=E: forall(E, lambda e, e_l=e_last:
                                 e.time <= e_l.time
                                                                     ), should_include_action=class_non_empty(E)),
                             )) for E in Actions if E != Measure]


    multi_output = []

    output = ""
    adj_hl = []
    red_result = False
    relations_constraint = get_relational_constraints(relations)
    if profiling:
        profiling_file = open("profiling_red.csv", 'w')
        profiling_file.write("raw_finish_time, proof_generation_time, proof_checking_time, raw_proof_size, raw_derivation_steps, trimmed_proof_size, trimmed_derivation_steps\n")
    csv_file = open("z3.csv", 'a')
    for i in range(len(rules)):
        sat_result = "unknown"
        if multi_entry:
            output = ""
            adj_hl = []

        if to_print:
            print("check rule_{}".format(i + 1))
        else:
            output += "check rule_{}\n".format(i + 1)

        rule = rules[i]
        others = rules[0:i] + rules[i + 1:]
        if profiling:
            # we want to measure the raw analysis time
            raw_start_time = time.time()
            check_property_refining(rule.get_neg_rule(), set(),
                                    [r.get_rule() for r in others] + relations_constraint +
                                    [measure_inv],
                                    Actions, [], True,
                                    min_solution=False,
                                    final_min_solution=True, restart=False, boundary_case=False,
                                    universal_blocking=False, vol_bound=VOL_BOUND,
                                    record_proof=None)

            raw_finish_time = time.time() - raw_start_time
            rule.get_neg_rule().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()

        if profiling:
            proof_generation_start_time = time.time()

        start = time.time()
        res = check_property_refining(rule.get_neg_rule(), set(first_inv),
                                      [r.get_rule() for r in others] + relations_constraint +
                                      [measure_inv] +
                                      first_inv,
                                      Actions, [], True,
                                      min_solution=False,
                                      final_min_solution=True, restart=False, boundary_case=False,
                                      universal_blocking=False, vol_bound=VOL_BOUND * 5,
                                      record_proof=check_proof)
        if profiling:
            proof_generation_time = time.time() - proof_generation_start_time

        if res == 2:
            rule.get_neg_rule().clear()
            clear_all(Actions)
            reset_rules(rules)
            clear_relational_constraints(relations)
            measure_inv.clear()
            [r.clear() for r in first_inv]
            derivation_rule.reset()

            if profiling:
                proof_generation_start_time = time.time()
            res = check_property_refining(rule.get_neg_rule(), set(first_inv),
                                          [r.get_rule() for r in others] + relations_constraint +
                                          [measure_inv] +
                                          first_inv,
                                          Actions, [], True,
                                          min_solution=False,
                                          final_min_solution=True, restart=False, boundary_case=False,
                                          universal_blocking=False, vol_bound=VOL_BOUND,
                                          record_proof=check_proof)

            if profiling:
                proof_generation_time = time.time() - proof_generation_start_time

        if isinstance(res, str):
            sat_result = "sat"
            if to_print:
                print("Not Redundant")
            else:
                output += "Not Redundant\n"

        elif res == 2:
            if to_print:
                print("Likely Redundant")
            else:
                output += "Likely Redundant\n"

        else:
            sat_result = "unsat"
            red_result = True

        if profiling:
            proof_checking_time = 0
            raw_proof_size = 0
            raw_derivation_steps = 0
            trimmed_proof_size = 0
            trimmed_derivation_steps = 0

        if res == 0 and check_proof:
            if profiling:
                raw_proof_size = os.path.getsize("proof.txt")
                raw_derivation_steps =  sum(1 for _ in open("proof.txt"))

            if profiling:
                proof_checking_start_time = time.time()

            result = check_and_minimize("proof.txt", "simplified.txt")

            if profiling:
                proof_checking_time = time.time() - proof_checking_start_time

            if profiling:
                trimmed_proof_size = os.path.getsize("simplified.txt")
                trimmed_derivation_steps = sum(1 for _ in open("simplified.txt"))

            if not result:
                print("warning Redundency info is not available")
                output += ("-" * 100 + '\n')
                clear_all(Actions)
                reset_rules(rules)
                measure_inv.clear()
                clear_relational_constraints(relations)
                [r.clear() for r in first_inv]
                derivation_rule.reset()
                rule.get_neg_rule().clear()
                continue

            UNSAT_CORE, derivation = result


            # print("*" * 100)
            print("UNSAT CORE")
            reasons = []
            for r in UNSAT_CORE:
                id = r.id
                if id == 0:
                    id = i
                elif id <= i:
                    id = id - 1
                else:
                    pass

                if id >= len(rules):
                    adjust_index = id
                    if model.relBlock and id - len(rules) < len(model.relBlock.relations):
                        rule_model = model.relBlock.relations[id - len(rules)]
                    else:
                        continue
                else:
                    adjust_index = id
                    rule_model = model.ruleBlock.rules[adjust_index]

                # start, end = rule_model._tx_position, rule_model._tx_position_end
                if adjust_index == i:
                    target = rule_model
                    # print("Redundant SLEEC rule:")
                    # print(model_str[start: end])
                    # print("-" * 100)
                else:
                    reasons.append(rule_model)
                    # reasons += (model_str[start: end]) + '\n' + "-" * 100 + '\n'

            local_index = {}

            start, end = target._tx_position, target._tx_position_end
            output += "Redundant SLEEC rule:\n"
            new_start = len(output)
            local_index[(start, end)] = new_start
            output += "{}\n".format(model_str[start: end])
            output += ("-" * 100 + '\n')
            output += "Because of the following SLEEC rule:\n"
            output += ("-" * 100 + '\n')
            for r in reasons:
                start, end = r._tx_position, r._tx_position_end
                new_start = len(output)
                local_index[(start, end)] = new_start
                output += "{}\n".format(model_str[start: end])
                output += ("-" * 100 + '\n')

            # print(output)

            print("TO BE HIGHLIGHTED")
            hls = get_high_light(derivation)
            for s, e in hls:
                print("{} : [{}, {}]".format(model_str[s: e], s, e))
                s, e = find_relative_pos(s, e, local_index)
                adj_hl.append((s, e))
                # print("{} : [{}, {}]".format(output[s: e], s, e))

            if multi_entry:
                multi_output.append((output, adj_hl))

        if profiling:
            print("sat_result: {}".format(sat_result))
            print("proof_generation_time: {}".format(proof_generation_time))
            csv_file.write("{},{},{},{},{}\n".format(filename, mode, i,  sat_result, proof_generation_time))
            profiling_file.write("{}, {}, {}, {}, {}, {}, {}\n".format(raw_finish_time, proof_generation_time,
                                                                     proof_checking_time, raw_proof_size, raw_derivation_steps,
                                                                     trimmed_proof_size, trimmed_derivation_steps))

        clear_all(Actions)
        reset_rules(rules)
        measure_inv.clear()
        clear_relational_constraints(relations)
        [r.clear() for r in first_inv]
        rule.get_neg_rule().clear()
        derivation_rule.reset()
        print("*" * 100)
        output += "*" * 100 + '\n'
    csv_file.close()
    if profiling:
        profiling_file.close()

    if multi_entry:
        return multi_output
    else:
        return red_result, output, adj_hl


def find_relative_pos(start, end, scopes):
    diff = end - start
    for s, e in scopes.keys():
        if s <= start <= e:
            # find the index
            diff_s = start - s
            new_s = scopes[(s, e)]
            return new_s + diff_s, new_s + diff_s + diff
    return -1, -1


def get_high_light(derivations):
    highlights = []
    for r in derivations:
        if isinstance(r, Fact):
            if r.text_ref:
                highlights.append(r.text_ref)
    return highlights


def reset_rules(rules):
    for r in rules:
        r.get_rule().clear()
        r.get_premise().clear()


def read_model_file(file_path):
    with open(file_path, 'r') as file:
        return file.read()


def parse_sleec(model_file, read_file=True):
    if read_file:
        model_str = read_model_file(model_file)
    else:
        model_str = model_file
    # Parse the model using the metamodel
    model = mm.model_from_str(model_str)
    Action_Mapping = parse_definitions(model.definitions)
    Actions = list(Action_Mapping.values())
    rules = parse_rules(model.ruleBlock, Action_Mapping)
    if model.concernBlock:
        concerns = parse_concerns(model.concernBlock, Action_Mapping)
    else:
        concerns = []

    if model.purposeBlock:
        purposes = parse_purposes(model.purposeBlock, Action_Mapping)
    else:
        purposes = []

    if model.relBlock:
        relations = parse_relations(model.relBlock, Action_Mapping)
    else:
        relations = []

    return model, rules, concerns, purposes, relations, Action_Mapping, Actions


#
# model_str = read_model_file("dressingrobot.sleec")
# check_red(model, rules, Action_Mapping, Actions, check_proof=True, model_str=model_str)

def check_input_red(model_str, multi_entry=False):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(model_str, read_file=False)
    res = check_red(model, rules, relations, Action_Mapping, Actions, check_proof=True, model_str=model_str,
                    multi_entry=multi_entry)
    # reset
    scalar_mask.clear()
    scalar_type.clear()
    registered_type.clear()
    text_ref.clear()
    return res


def check_input_conflict(model_str, multi_entry=False):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(model_str, read_file=False)
    res = check_conflict(model, rules, relations, Action_Mapping, Actions, check_proof=True, model_str=model_str,
                         multi_entry=multi_entry)
    # reset
    scalar_mask.clear()
    scalar_type.clear()
    registered_type.clear()
    text_ref.clear()
    return res


def check_input_purpose(model_str, multi_entry=False):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(model_str, read_file=False)
    res = check_purposes(model, purposes, rules, relations, Action_Mapping, Actions, check_proof=True,
                         model_str=model_str,
                         multi_entry=multi_entry)
    # reset
    scalar_mask.clear()
    scalar_type.clear()
    registered_type.clear()
    text_ref.clear()
    return res


def check_input_concerns(model_str):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(model_str, read_file=False)
    res = check_concerns(model, rules, concerns, relations, Action_Mapping, Actions, model_str=model_str)
    # reset
    scalar_mask.clear()
    scalar_type.clear()
    registered_type.clear()
    text_ref.clear()
    return res



from argparse import ArgumentParser


def parse_and_check_conflict(filename):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(filename,
                                                                                       read_file=True)
    res = check_conflict(filename, "conflict", model, rules, relations, Action_Mapping, Actions, check_proof=False, profiling=True)
    return res


def parse_and_check_red(filename):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(filename,
                                                                                       read_file=True)
    res = check_red(filename, "redundancy", model, rules, relations, Action_Mapping, Actions, check_proof=False,profiling=True)
    return res


def parse_and_check_concern(filename):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(filename,
                                                                                       read_file=True)
    res = check_concerns(filename, "concern", model, rules, concerns, relations, Action_Mapping, Actions)
    return res


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument('--filename', help="SLEEC file to analyze", type=str)
    parser.add_argument('--analysis', help='What the analysis to run: redundancy/conflict/concern', type=str)
    args = parser.parse_args()
    supported_mode = {"redundancy": parse_and_check_red, "conflict": parse_and_check_conflict,
                      "concern": parse_and_check_concern}
    analysis = args.analysis
    if analysis not in supported_mode:
        print("unsupported analysis mode, please choice one of the analysis mode redundancy/conflict/concern")
        print("running redundancy for default")
    analysis_func = supported_mode.get(analysis, parse_and_check_red)
    print("analysis_func: {}".format(analysis_func))
    analysis_func(args.filename)
#
#
# if __name__ == "__main__":
#     model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec("test_files/test.sleec", read_file=True)
#     res = check_red(model, rules, relations, Action_Mapping, Actions, check_proof=False, profiling=True)
# model, rules, Action_Mapping, Actions,_ = parse_sleec("safescade/safescade.sleec")


# Measure = Action_Mapping["Measure"]
# measure_inv = forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2)))
#
# i =4
# print("check R5 red")
# others = rules[0:i] + rules[i+1:]
# res = check_property_refining(NOT(rules[i].get_rule()), set(),[r.get_rule() for r in others] + [measure_inv], Actions, [], True,
#                         min_solution=False,
#                         final_min_solution=True, restart=False, boundary_case=False, universal_blocking=False, record_proof=True)
#
#

# if res == 0:
#     UNSAT_CORE, derivation = check_and_minimize("proof.txt", "simplified.txt")
#     print("*" * 100)
#     print("UNSAT CORE")
#     reasons = ""
#     for r in UNSAT_CORE:
#         id = r.id
#         if id == 0:
#             id = i
#         rule_model = model.ruleBlock.rules[id]
#         start, end = rule_model._tx_position, rule_model._tx_position_end
#         if id == i:
#             print("Redundant SLEEC rule:")
#             print(model_str[start: end])
#             print("-" * 100)
#         else:
#             reasons += (model_str[start: end]) + '\n' + "-" * 100 + '\n'
#
#     print(reasons)
#
#     print("*" * 100)
