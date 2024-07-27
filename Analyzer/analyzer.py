from Analyzer.logic_operator import *
from Analyzer.type_constructor import snap_shot
from Analyzer.trace_ult import print_trace
import copy
from Analyzer.derivation_rule import Proof_Writer

'''
Check the validity of a trace implied by the model from
solving a given set of constraints. Stop at the 
first rule that is violated by the trace 
'''
action_iteration_bound = 1000


def get_all_actions(ACTION):
    res = []
    for ACT in ACTION:
        res += ACT.collect_list
    return res


def complete_clear_actions(ACTION):
    for ACT in ACTION:
        ACT.collect_list.clear()
        ACT.temp_collection_set = OrderedSet()
        ACT.syn_collect_list.clear()
        ACT.additional_constraint.clear()
        ACT.snap_shot.clear()
        ACT.EQ_CLASS = [OrderedSet()]
        ACT.Uncollected = OrderedSet()
        ACT.inv = []
        ACT.presence_counter = 0
        # TODO, may need to clear indexs


def clear_caches():
    C_OR.cache.clear()
    C_AND.cache.clear()


def clear_Exist_cache():
    Exists.Temp_ACTs.clear()
    Exists.check_ACTS.clear()
    Exists.new_included.clear()
    Exists.pending_defs.clear()
    Exists.hint_barrier = False


def clear_Forall_cache():
    text_ref.clear()
    shadow_dict.clear()
    minimize_memory.clear()
    action_activity.clear()
    Forall.pending_defs.clear()
    C_OR.cache.clear()
    C_AND.cache.clear()
    learned_inv.clear()
    model_action_mapping.clear()


def clear_Function_cache():
    Function.Function_cache.clear()
    Predicate.Predicate_Cache.clear()


def clear_all(ACTION, rules=None):
    complete_clear_actions(ACTION)
    clear_Exist_cache()
    clear_Forall_cache()
    clear_Function_cache()
    clear_caches()
    considered_object.clear()
    considered_constraint.clear()
    if rules is not None:
        clear_rules(rules)


def clear_rules(rules):
    for rule in rules:
        if isinstance(rule, Exists):
            rule.proof_lit = None
            rule.act_include = None
            rule.act_non_include = None
            rule.func.result_cache.clear()
            if rule.func.op is not None:
                rule.func.op.result_cache.clear()
        if isinstance(rule, Forall):
            rule.proof_lit = None
            rule.considered.clear()
            rule.pending_defs.clear()
            rule.func.result_cache.clear()
            if rule.func.op is not None:
                rule.func.op.result_cache.clear()


considered_object = OrderedSet()
considered_constraint = []


def get_all_constraint(ACTION, full=True):
    global considered_constraint
    res_constraint = []
    for ACT in ACTION:
        for act in ACT.collect_list:
            if act not in considered_object:
                for delayed_func in act.delayed_constraint:
                    result = delayed_func()
                    considered_constraint.append(result)
                    if not full:
                        res_constraint.append(result)

                considered_constraint.append(act.constraint)
                if not full:
                    res_constraint.append(act.constraint)
                considered_object.add(act)
        for act in ACT.temp_collection_set:
            if act not in considered_object:
                for delayed_func in act.delayed_constraint:
                    result = delayed_func()
                    considered_constraint.append(result)
                    if not full:
                        res_constraint.append(result)

                considered_constraint.append(act.constraint)
                if not full:
                    res_constraint.append(act.constraint)
                considered_object.add(act)
    if full:
        return considered_constraint
    else:
        return res_constraint


def clear_actions(Action):
    # Action.collect_list.clear()
    Action.syn_collect_list.clear()


def clear_all_action(ACTION):
    for Action in ACTION:
        clear_actions(Action)


def snap_shot_all(ACTION):
    for Act in ACTION:
        snap_shot(Act)


def action_changed(ACTION):
    changed = []
    for Act in ACTION:
        if len(Act.snap_shot) < len(Act.collect_list):
            changed.append(Act)
    return changed


def check_trace(model, complete_rules, rules, stop_at_first=True, axioms=None):
    """
    check sat sol and refine rules ( constraint expansion )
    """
    solver = Solver(name="z3", random_seed=43)
    if axioms:  # presumed rules?
        solver.add_assertion(axioms)
    # assert(len(Forall.pending_defs) == 0)
    parital_model = [EqualsOrIff(k, v) for k, v in model]  # what is parital_model ?
    solver.add_assertion(And(parital_model))
    result = OrderedSet()
    called = False
    for rule in complete_rules:
        if rule in rules:
            continue
        else:
            # solver.push()
            constraint = encode(rule, include_new_act=False, disable=True)
            solver.add_assertion(constraint)
            constraints, vars = get_temp_act_constraints(checking=True)
            solver.add_assertion(And(constraints))
            solved = solver.solve(vars)
            called = True
            # solver.pop()
            if not solved:
                # print("add rule {}".format(to_string(rule)))
                result.add(rule)
                if stop_at_first:
                    return result, None
            else:
                # there might be newly enforeced assignment, and make them explicit
                continue
    if called:
        model = solver.get_model()
    return result, model


def inductive_checking(property, rules, complete_rules, ACTION, state_action, minimized=False):
    rules = OrderedSet(rules)
    snap_shot_all(ACTION)
    application_rounds = 0
    inductive_assumption_table = dict()
    prop = encode(property, include_new_act=False)

    new_rules = set(rules)
    should_calibrate = True
    s = Solver("z3")
    s.add_assertion(prop)
    while application_rounds < action_iteration_bound:
        print(application_rounds)
        while (action_changed(ACTION) or should_calibrate):
            should_calibrate = False
            snap_shot_all(ACTION)
            encode(property, include_new_act=False)
            for p in rules:
                temp_res = encode(p, include_new_act=False)
                if p in new_rules:
                    s.add_assertion(temp_res)

        new_rules.clear()
        print("end encoding")
        s.add_assertion(And(get_all_constraint(ACTION, full=False)))
        add_forall_defs(s)
        add_exist_defs(s)

        solved = s.solve()
        if solved:
            s.push()
            s.add_assertion(And(get_temp_act_constraints()))
            solved = s.solve()
            if solved:
                model = s.get_model()
                print_trace(model, ACTION, state_action)
                # check trace
                res, _ = check_trace(model, complete_rules, rules, stop_at_first=True)
                if len(res) == 0:
                    print("find trace")
                    print_trace(model, ACTION, state_action)
                    return False
                else:
                    # print("need to add more rules")
                    rules = rules.union(res)
                    new_rules = res
                    should_calibrate = True
                    s.pop()
            else:
                s.pop()
                if minimized:
                    # print("start minimizing")
                    old_rule = copy.copy(rules)
                    get_temp_act_constraint_minimize(s, complete_rules, [],
                                                     inductive_assumption_table=inductive_assumption_table,
                                                     addition_actions=None, round=application_rounds,
                                                     ignore_class=state_action)
                    new_rules = rules - old_rule
                else:
                    model = s.get_model()
                    analyzing_temp_act(model)
                # print("need to increase domain")
                application_rounds += 1
        else:
            print("unsat")
            return True
    # print(serialize(result))
    print("reaching limit, bounded unsat")
    return True


def prove_by_induction(property, rules, complete_rules, ACTION, state_action, minimized=False):
    # first check init
    res = inductive_checking(property, rules, complete_rules, ACTION, state_action, minimized)

    clear_all(ACTION, list(rules) + [property])
    return res


import random


# ACTION is classes
# rules: consider for now
# new_rules: consider later

def check_property_refining(property, rules, complete_rules, ACTION, state_action, minimized=True, vol_bound=500,
                            disable_minimization=False, min_solution=False, final_min_solution=False,
                            boundary_case=False, universal_blocking=False, restart=False, ignore_state_action=False,
                            axioms=None, record_proof=False, ret_model=False, scalar_mask=None, unsat_mode=False):
    """
    main function to solve the formula
    """
    # print the configuration setting
    print("solving under config: restart {}, bcr {}, ub {}, min {}".format(restart, boundary_case, universal_blocking,
                                                                           min_solution))
    rules = OrderedSet(rules)  # a set of rules that remember the rules order
    current_min_solution = False
    out_of_bound_warning = False
    application_rounds = 1
    opt_sol_check = False

    if record_proof:  # record the proof
        proof_writer = Proof_Writer("proof.txt")
        proof_writer.add_input_rule(property)  # add the rule that we want to prove
        for rule in complete_rules:
            proof_writer.add_input_rule(rule)  # add the background rules (finished by the user)
    else:  # we do not record the proof
        proof_writer = None
        # for rule in complete_rules:
        #     proof_writer.add_input_rule(rule)

    if ignore_state_action:
        ignore_actions = state_action  # special funcs ? what kind of funcs are these ?
        #  Actions do not want take account of e.g. timepoint
    else:
        ignore_actions = None

    if boundary_case:  # for optimization
        inductive_assumption_table = dict()  # a dictionary that stores the inductive assumptions. for boundary cases ?
    else:
        inductive_assumption_table = None

    new_rules = set(rules)
    should_calibrate = True
    s = Solver("z3", unsat_cores_mode=None, random_seed=43)  # z3 solver （ oriented from SMT solver ）
    if axioms:
        s.add_assertion(axioms)

    prop = encode(property, include_new_act=True, proof_writer=proof_writer, unsat_mode=unsat_mode)  # ground the
    # property and do overapproximation
    s.add_assertion(prop)  # add the property to the solver. is the assertion here like a constraint ?
    # print(serialize(prop))
    # restart control

    restart_threshold = 10  # the threshold for restart for optimization
    round_without_new_rules = 0  # initialize to track the number of rounds without new rules
    eq_assumption = OrderedSet()  # consider the set of equality assumptions

    while application_rounds < action_iteration_bound:
        # print(application_rounds)

        # reset_underapprox(s)
        # handle restart
        if restart and round_without_new_rules > restart_threshold:
            # clear the rules
            print("restarted")
            rules.clear()
            # random.shuffle(complete_rules)
            # rules = set(get_background_rules(boundary_case))
            # we still want to add background rules
            # add_background_theories(ACTION, state_action, rules, add_actions=False)
            round_without_new_rules = 0
            restart_threshold = int(restart_threshold * 1.5)  # increase the threshold

        while action_changed(ACTION) or should_calibrate:  # optimization speed up domain expansion immediately
            # expand on specific constraints
            should_calibrate = False
            snap_shot_all(ACTION)
            encode(property, include_new_act=False, proof_writer=proof_writer, unsat_mode=unsat_mode)
            for p in rules:
                if p in new_rules:
                    # if record_proof:
                    #     proof_writer.add_input_rule(p)
                    temp_res = encode(p, include_new_act=False, proof_writer=proof_writer, unsat_mode=unsat_mode)
                    s.add_assertion(temp_res)  # only add the new rules
                    # print(serialize(temp_res))
                else:
                    encode(p, include_new_act=False, proof_writer=proof_writer, unsat_mode=unsat_mode)

        # for ACt in ACTION:
        #     print(ACt)
        #     print(ACt.collect_list)
        #     print(ACt.snap_shot)
        #     print("sus:")
        #     for act in ACt.temp_collection_set:
        #         print(act)
        new_rules.clear()  # have already added the new rules
        # print("end encoding")

        # now update the constraints
        update_underapprox(s)
        over_constraints, over_vars = update_overapprox()  # ignore for now
        for c in over_constraints:
            if c != TRUE():
                s.add_assertion(c)

        add_forall_defs(s)  # add the forall definitions
        add_exist_defs(s)  # add the exist definitions
        add_predicate_constraint(s)  # add the predicate constraints
        all_cons = And(get_all_constraint(ACTION, full=False))
        s.add_assertion(all_cons)
        # print(serialize(all_cons))

        if current_min_solution:  # smaller solution, set to true if already find sol
            solved = True
        else:
            # solved = s.solve(over_vars.union(eq_assumption))
            solved = solver_under_eq_assumption(s, over_vars, eq_assumption)

        if solved:  # over approx is sat
            save_model = s.get_model()  # get the model
            # Summation.frontier = new_frontier
            # Summation.collections = new_summation

            constraints, vars = get_temp_act_constraints()
            for c in constraints:
                if c != TRUE():  # if the constraint is not true
                    s.add_assertion(c)  # add the constraint
                    # print("add temp constraint {}".format(serialize(c)))
            # s.add_assertion(And(constraints))
            vars = vars.union(over_vars)  # add the overapproximation variables

            if current_min_solution:  # know over and under sat
                solved = True  # under is sat
            else:
                # solved = s.solve(vars)
                solved = solver_under_eq_assumption(s, vars, eq_assumption)  # under

            if solved:  # under is sat
                model = s.get_model()  # get the model
                # print_trace(model, ACTION, state_action, ignore_class=state_action)
                # check trace
                res, model = check_trace(model, complete_rules, rules, stop_at_first=True)  # check the trace to see
                # if it is valid
                if len(res) == 0:  # num of rules in complete rules(whole) been falsified
                    if min_solution:  # want to minimize solution
                        model = mini_solve(s, get_all_actions(ACTION), vars=vars, eq_vars=eq_assumption,
                                           ignore_class=ignore_actions)  # try t0 minimize the solution with cur domain
                        # print("mini-trace")
                    print("find trace")  # we found trace ( solution )
                    current_best = model
                    vol, _ = print_trace(model, ACTION, state_action, ignore_class=state_action, should_print=False)
                    # diff between mini_solve and get_temp_act_constraint_minimize ? why check the same thing twice ?
                    if min_solution or (out_of_bound_warning and vol > vol_bound):
                        # vol > volbound : max of vol sol have been reached
                        # s.pop()
                        # if finding the minimum solution or the volume is out of bound,
                        # try to minimize the solution more

                        # try to minimize the solution more , over approx with minimum sol
                        model = get_temp_act_constraint_minimize(s, rules, over_vars, eq_assumption,
                                                                 addition_actions=get_all_actions(ACTION),
                                                                 round=application_rounds,
                                                                 disable_minimization=disable_minimization,
                                                                 ignore_class=ignore_actions, relax_mode=False)
                        new_vol, _ = print_trace(model, ACTION, state_action, should_print=False,
                                                 ignore_class=state_action, check_sum=True)
                        print(new_vol, vol)
                        if new_vol > vol_bound:  # if the new volume is out of bound
                            print("Bounded UNSAT")
                            return 2
                        if new_vol >= vol:  # want the minimization one, vol is under bound but not enough
                            if not opt_sol_check:  # ignore for now
                                opt_sol_check = True
                            else:  # check if the solution is optimal
                                _, str_output = print_trace(current_best, ACTION, state_action,
                                                            ignore_class=state_action,
                                                            should_print=True, scaler_mask=scalar_mask)
                                print("opt vol is {}".format(vol))
                                print("solution is opt")

                                if ret_model:
                                    return str_output, current_best
                                else:
                                    return str_output
                        else:  # if the new volume is smaller than the previous one
                            print("A better result may exist")
                            current_min_solution = True
                    else:  # did not have out of bound warning or finding the minimum solution
                        vol, str_output = print_trace(current_best, ACTION, state_action, ignore_class=state_action,
                                                      should_print=True,
                                                      scaler_mask=scalar_mask)
                        print("vol: {}".format(str(vol)))
                        if ret_model:
                            return str_output, current_best
                        else:
                            return str_output
                else:  # res is not empty still not sat
                    # print("need to add more rules")
                    round_without_new_rules = 0  # will add new rules that falsified the cur domain
                    rules = rules.union(res)
                    new_rules = res
                    should_calibrate = True
                    # s.pop()
            else:  # not solved
                round_without_new_rules += 1
                # s.pop()
                if minimized:  # not imprtant but more performance
                    # print("start minimizing")
                    if out_of_bound_warning:  # A* search
                        addition_actions = get_all_actions(ACTION)  # get all obejects for the spe act
                    else:  # gbfs
                        addition_actions = None
                    # expand the domain, considering mim sol( either expand domain A*, also minimizing domain expansion)
                    new_model = get_temp_act_constraint_minimize(s, complete_rules, over_vars, eq_assumption,
                                                                 addition_actions=addition_actions,
                                                                 round=application_rounds,
                                                                 disable_minimization=disable_minimization,
                                                                 ignore_class=ignore_actions,
                                                                 inductive_assumption_table=inductive_assumption_table,
                                                                 relax_mode=not current_min_solution,
                                                                 ub=universal_blocking, over_model=save_model)

                    if new_model is None:  # trace save model
                        new_volume, _ = print_trace(save_model, ACTION, state_action, should_print=False,
                                                    ignore_class=state_action)
                    else:  # trace new model
                        new_volume, _ = print_trace(new_model, ACTION, state_action, should_print=False,
                                                    ignore_class=state_action)
                        new_volume += 1

                    # print_trace(new_model, ACTION, state_action, should_print=True, ignore_class=[], solver=s,
                    #             assumption=over_vars)
                    # print("start cleanning")
                    summation_clean_up(s, over_vars)  # clean up the summation  # dont worry
                    for ACT in ACTION:  # clean up the action
                        clean_up_action(s, over_vars, ACT)  # dont worry
                    # print("start action merging ")
                    # print("{} assumptions remained".format(len(eq_assumption)))
                    if new_model:
                        model_based_gc(ACTION, new_model, s, eq_assumption, over_vars, strengthen=False,
                                       value_bound_assumption=False)  # dont worry
                    # print("{} assumptions generated".format(len(eq_assumption)))
                    if new_volume > vol_bound:  # if the new volume is out of bound
                        if out_of_bound_warning:  # if already have out of bound warning
                            print("bounded UNSAT")
                            return 2
                        else:  # if not have out of bound warning
                            # print("entering strict min search mode")
                            out_of_bound_warning = True
                else:  # get the sol in over approx
                    model = s.get_model()
                    analyzing_temp_act(model)

                # print("need to increase domain")
                application_rounds += 1

        else:
            if record_proof:  # dont worry
                proof_writer.derive_unsat(considered_constraint)
            print("domain size {}".format(str(len(get_all_actions(ACTION)))))
            print("unsat")
            return 0
    # print(serialize(result))
    print("reaching limit, bounded unsat")  # if reaching the limit
    return -1


def solver_under_eq_assumption(solver, assumption, eq_assumption):
    satisfying = solver.solve(assumption.union(eq_assumption))
    while not satisfying:
        assumptions = solver.z3.unsat_core()
        invalid_assumption = [solver.converter.back(t) for t in assumptions]
        invalid_assumption = set([t for t in invalid_assumption if t in eq_assumption])
        if invalid_assumption:
            for t in invalid_assumption:
                solver.add_assertion(NOT(t))
                eq_assumption.remove(t)
            satisfying = solver.solve(assumption.union(eq_assumption))
        else:
            return False
    return True


def solve_fol(rules, complete_rules, ACTION, state_action, minimized=False, vol_bound=500,
              disable_minimization=False, min_solution=False, final_min_solution=False,
              boundary_case=False, universal_blocking=False, restart=False, ignore_state_action=False,
              axioms=None, record_proof=False, ret_model=False, scalar_mask=None):
    return check_property_refining(TRUE(), rules, complete_rules, ACTION, state_action, minimized=minimized,
                                   vol_bound=vol_bound,
                                   disable_minimization=disable_minimization, min_solution=min_solution,
                                   final_min_solution=final_min_solution,
                                   boundary_case=boundary_case, universal_blocking=universal_blocking, restart=restart,
                                   ignore_state_action=ignore_state_action,
                                   axioms=axioms, record_proof=record_proof, ret_model=ret_model,
                                   scalar_mask=scalar_mask)
