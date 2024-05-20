FORALL = "forall"
EXISTS = "exists"


class S_Quantifier():

    def __init__(self, name, s_class, expr):
        self.name = name
        self.s_class = s_class
        self.expr = expr

    def match(self, rhs, subs):
        return self.s_class == rhs.s_class and \
            match(self.expr, rhs.expr, subs | {self.name+'_': rhs.name+'_'})


class S_Forall(S_Quantifier):
    pass


class S_Exist(S_Quantifier):
    pass

def substitute(lhs: str, subs: dict[str:str]):
    for s, t in subs.items():
        lhs = lhs.replace(s, t)
    return lhs


def match(lhs, rhs, subs):
    if isinstance(lhs, list) and isinstance(rhs, list):
        if len(lhs) == len(rhs):
            result = True
            for i, j in zip(lhs, rhs):
                result = result and match(i, j, subs)
            return result
    elif isinstance(lhs, str) and isinstance(rhs, str):
        return substitute(lhs, subs) == rhs
    elif isinstance(lhs, S_Forall) and isinstance(rhs, S_Forall):
        return lhs.match(rhs, subs)
    elif isinstance(lhs, S_Exist) and isinstance(rhs, S_Exist):
        return lhs.match(rhs, subs)

    return False


def is_terminal_symbol(expr):
    return isinstance(expr, str)


def parse_forall(contents):
    head = _s_parse(contents[0])
    class_name = _s_parse(contents[1])
    expression = _s_parse(contents[2])
    return S_Forall(head, class_name, expression)


def parse_exists(contents):
    head = _s_parse(contents[0])
    class_name = _s_parse(contents[1])
    expression = _s_parse(contents[2])
    return S_Exist(head, class_name, expression)


def s_tokenize(expr: str):
    current = []
    stack = []
    cur_str = ''
    for char in expr:
        if char == '(':
            stack.append(current)
            current = []
        elif char == ')':
            if cur_str:
                current.append(cur_str)
                cur_str = ''
            if stack:
                new_current = stack.pop()
                new_current.append(current)
                current = new_current
            else:
                return current
        elif char == ' ':
            if cur_str:
                current.append(cur_str)
            cur_str = ''
        else:
            cur_str += char

    return current
    # tokens = []
    # _s_tokenize(expr, 0, tokens, '')
    # return tokens


# def _s_tokenize(expr:str, index, content, cur_str):
#     if index >= len(expr):
#         return
#     else:
#         char = expr[index]
#         if char == '(':
#             new_content = []
#             new_index = _s_tokenize(expr, index+1, new_content, '')
#             content.append(new_content)
#             return _s_tokenize(expr, new_index+1, content, '')
#         elif char == ')':
#             if cur_str:
#                 content.append(cur_str)
#             return index
#         else:
#             if char == ' ':
#                 if cur_str:
#                     content.append(cur_str)
#                 return _s_tokenize(expr, index + 1, content, '')
#             else:
#                 cur_str+=char
#                 return _s_tokenize(expr, index+1, content, cur_str)

def _s_parse(tokens):
    if is_terminal_symbol(tokens):
        return tokens
    else:
        # there are many cases, we first get the function that is being applied
        func = _s_parse(tokens[0])
        if func == FORALL:
            return parse_forall(tokens[1:])
        elif func == EXISTS:
            return parse_exists(tokens[1:])
        else:
            return [_s_parse(s) for s in tokens]


def is_binary(expr):
    return isinstance(expr, list) and len(expr) == 3


BinaryOP = {"<=", ">=", ">", "<", "==", "!="}


def is_leaf(expr):
    if is_binary(expr):
        op = expr[1]
        return op in BinaryOP
    else:
        return False


def is_chain(expr, token):
    if isinstance(expr, list) and len(expr) >= 3:
        i = 1
        while i < len(expr):
            if expr[i] == token:
                i += 2
            else:
                return False
        return True
    return False

def is_conjunctions(expr):
    return is_chain(expr, "&")

def is_disjunctions(expr):
    return is_chain(expr, "|")


def is_negation(expr):
    return isinstance(expr, list) and len(expr) == 2 and expr[0] == "!"


def normalize(expr, pos=True):
    if isinstance(expr, str):
        if pos:
            return expr
        else:
            return ["!", expr]
    else:
        if is_leaf(expr):
            if pos:
                return expr
            else:
                return ["!", expr]
        else:
            if is_negation(expr):
                body = expr[1]
                if pos:
                    return normalize(body, pos=False)
                else:
                    return normalize(body, pos=True)
            else:
                if isinstance(expr, S_Forall):
                    if pos:
                        return S_Forall(expr.name, expr.s_class, normalize(expr.expr, pos))
                    else:
                        return S_Exist(expr.name, expr.s_class, normalize(expr.expr, pos=False))
                elif isinstance(expr, S_Exist):
                    if pos:
                        return S_Exist(expr.name, expr.s_class, normalize(expr.expr, pos))
                    else:
                        return S_Forall(expr.name, expr.s_class, normalize(expr.expr, pos=False))
                elif is_conjunctions(expr):
                    result = []
                    for i in range(len(expr)):
                        if i & 1:
                            if pos:
                                result.append("&")
                            else:
                                result.append("|")
                        else:
                            if pos:
                                result.append(normalize(expr[i], pos=True))
                            else:
                                result.append(normalize(expr[i], pos=False))
                    return result
                elif is_disjunctions(expr):
                    result = []
                    for i in range(len(expr)):
                        if i & 1:
                            if pos:
                                result.append("|")
                            else:
                                result.append("&")
                        else:
                            if pos:
                                result.append(normalize(expr[i], pos=True))
                            else:
                                result.append(normalize(expr[i], pos=False))
                    return result
                else:
                    if pos:
                        return expr
                    else:
                        return ["!", expr]


def NNF_check(lhs, rhs, subs):
    n_l = normalize(lhs)
    n_r = normalize(rhs)
    return match(n_l, n_r, subs)


def s_parse(expr: str):
    return _s_parse(s_tokenize(expr))


GT_Relation = {("<->", '->'), ("<->", '<-')}


def s_ge(token1, token2):
    return token1 == token2 or (token1, token2) in GT_Relation


if __name__ == "__main__":
    test_str1 = "(forall p_Declare_Leader_0_0 Declare_Leader_0 ( (! p_Declare_Leader_0_0_presence) | ((exists p_Message_0_1 Message_0 (p_Message_0_1_presence & ((p_Message_0_1_message = ID_1) & (p_Message_0_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_1_1 Message_1 (p_Message_1_1_presence & ((p_Message_1_1_message = ID_1) & (p_Message_1_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_2_1 Message_2 (p_Message_2_1_presence & ((p_Message_2_1_message = ID_1) & (p_Message_2_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_3_1 Message_3 (p_Message_3_1_presence & ((p_Message_3_1_message = ID_1) & (p_Message_3_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_4_1 Message_4 (p_Message_4_1_presence & ((p_Message_4_1_message = ID_1) & (p_Message_4_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_5_1 Message_5 (p_Message_5_1_presence & ((p_Message_5_1_message = ID_1) & (p_Message_5_1_time <= p_Declare_Leader_0_0_time)))))))"
    test_str2 = "(forall p_Declare_Leader_0_0 Declare_Leader_0 ( (! p_Declare_Leader_0_0_presence) | ((exists p_Message_0_1 Message_0 (p_Message_0_1_presence & ((p_Message_0_1_message = ID_1) & (p_Message_0_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_1_1 Message_1 (p_Message_1_1_presence & ((p_Message_1_1_message = ID_1) & (p_Message_1_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_2_1 Message_2 (p_Message_2_1_presence & ((p_Message_2_1_message = ID_1) & (p_Message_2_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_3_1 Message_3 (p_Message_3_1_presence & ((p_Message_3_1_message = ID_1) & (p_Message_3_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_4_1 Message_4 (p_Message_4_1_presence & ((p_Message_4_1_message = ID_1) & (p_Message_4_1_time <= p_Declare_Leader_0_0_time)))) & (exists p_Message_5_1 Message_5 (p_Message_5_1_presence & ((p_Message_5_1_message = ID_1) & (p_Message_5_1_time <= p_Declare_Leader_0_0_time)))))))".replace(
        "p_Declare_Leader_0_0", "wtf")
    res1 = s_parse(test_str1)
    res2 = s_parse(test_str2)
    print(match(res1, res2, {}))
