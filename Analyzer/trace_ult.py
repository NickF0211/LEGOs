from ordered_set import OrderedSet

from logic_operator import _SUMObject, exist, EQ, forall, Implication, OR
def multisort(xs, specs):
    for key, reverse in reversed(specs):
        xs.sort(key=key, reverse=reverse)
    return xs



def print_trace(model, ACTION, state_action, include_temp = False, should_print=True, ignore_class = None, check_sum = False,
                scaler_mask = None):
    output_str = ""
    all_objects = []
    for action in ACTION:
        if include_temp:
            all_objects += list(set(action.collect_list).union(action.temp_collection_set))
        else:
            all_objects += action.collect_list

    filtered_objects = filter(lambda obj: model.get_py_value(obj.presence), all_objects)
    sorted_objects = multisort(list(filtered_objects), [(lambda obj: model.get_py_value(obj.time) if hasattr(obj, "time") else -1,
                                                         False),
                     (lambda obj: type(obj) in state_action, True)])
    old_res = ""
    vol  = 0
    sum_class = OrderedSet()
    entry = OrderedSet()
    for obj in sorted_objects:
        if ignore_class is not None and type(obj) in ignore_class:
            continue
        if check_sum and isinstance(obj, _SUMObject):
            sum_class.add(obj.input_type)

        res = obj.get_record(model, debug= False, mask = scaler_mask)
        if res not in entry:
            entry.add(res)
            if should_print:
                if obj not in type(obj).collect_list:
                    res = "*"+res
                print(res)
                output_str += "{}\n".format(res)
            vol += 1
        old_res = res

    return len(entry) + len(sum_class), output_str


def model_based_inst(model, ACTION, completeness = False, time=-1, measure_class = None, should_print=False, scaler_mask = None):
    output_str= ""
    all_objects = []
    results = []
    for action in ACTION:
        all_objects += action.collect_list

    filtered_objects = filter(lambda obj: model.get_py_value(obj.presence) and hasattr(obj, "time"), all_objects)
    sorted_objects = list(filtered_objects)

    objs_by_action= {}
    for ACT in ACTION:
        objs_by_action[ACT] = []

    c_time = model[time]
    for obj in sorted_objects:
        model_obj = obj.model_projection(model)
        if int(str(model_obj.time)) > int(str(c_time)) and (type(obj) != measure_class):
            continue

        if should_print:
            if int(str(model_obj.time)) <= int(str(c_time)):
                res = obj.get_record(model, debug=False, mask=scaler_mask)
                if obj not in type(obj).collect_list:
                    res = "*" + res
                output_str += "{}\n".format(res)

        results.append(exist(type(obj), lambda copy_obj, model_obj = model_obj: EQ(copy_obj, model_obj)))
        if completeness:
            objs_by_action[type(obj)].append(model_obj)

    if completeness:
        c_time = model[time]
        for ACT in ACTION:
            if measure_class is not None and ACT == measure_class:
                continue
            objs = objs_by_action[ACT]
            results.append(forall(ACT, lambda act_obj, objs=objs, c_time=c_time: Implication(act_obj.time < c_time,
                                                                             OR([EQ(act_obj, obj) for obj in objs])
                                                                              ) ) )

    return results, output_str



