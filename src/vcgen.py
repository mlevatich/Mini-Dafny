#!/usr/bin/env python3

# for printing and file reading
import sys

# dictionary of variables/arrays z3 will eventually need declared.
var_dict = {}
var_append = 0
arr_dict = {}
arr_append = 0

# helper to get a new variable which is not taken by var_dict.
# used by compute_wp() to get the tmp variable that results from havoc.
def get_var():
    global var_append, var_dict
    var = 'iiii' + str(var_append)
    var_append += 1
    while (var in var_dict):
        var = var = 'iiii' + str(var_append)
        var_append += 1
    var_dict[var] = 1
    return var

# helper to get a new array for the same purposes as above
def get_arr():
    global arr_append, arr_dict
    arr = 'aaaa' + str(arr_append)
    arr_append += 1
    while (arr in arr_dict):
        arr = 'aaaa' + str(arr_append)
        arr_append += 1
    arr_dict[arr] = 1
    return arr


# helper to find all variable names within an unprocessed program tree.
# used by loops to figure out which variables to havoc.
def find_vars(tree):
    vars = set()
    if tree[0] == 'Assign':
        return tree[1]
    elif tree[0] == 'ParAssign':
        return tree[1] + tree[2]
    for i in range(len(tree)):
        if isinstance(tree[i], list):
            vars.update(find_vars(tree[i]))
    return list(vars)


# helper to replace all occurances of a variable in a (preprocessed) tree B.
# used by compute_wp() to havoc a variable.
def replace_var(var, rep, B):
    new_B = []
    for i in range(len(B)):
        if isinstance(B[i], list):
            new_B.append(replace_var(var, rep, B[i]))
        elif B[i] == var:
            new_B.append(rep)
        else:
            new_B.append(B[i])
    return new_B


# turn a string into a tree by parsing for parentheses
def str_to_tree(prog_string):
    children = []
    name_delim = prog_string.find('(')
    if name_delim == -1:
        return [prog_string]
    children.append(prog_string[:name_delim])
    prog_string = prog_string[name_delim+1:]
    start = 0
    parens = 0
    for i in range(0,len(prog_string)):
        if prog_string[i] == '(':
            parens += 1
        if prog_string[i] == ')':
            parens -= 1
        if parens == -1 or (parens == 0 and prog_string[i] == ','):
            substr = prog_string[start:i]
            start = i+1
            children.append(str_to_tree(substr))
    return children


# takes an assertion, or an arithmetic or boolean expression,
# and converts it into a tree of reverse-polish-notation operations
def preprocess(exp):
    RPN_tree = []
    type = exp[0]

    if type == 'List':
        if len(exp) == 2:
            RPN_tree = preprocess(exp[1])
        else:
            RPN_tree.append('and')
            RPN_tree.append(preprocess(exp[1]))
            RPN_tree.append(preprocess(['List'] + exp[2:]))

    elif type == 'Var':
        var_dict[exp[1][0]] = 1
        RPN_tree.append(exp[1][0])

    elif type == 'Num':
        RPN_tree.append(exp[1][0])

    elif type == 'Add' or type == 'Sub' or type == 'Mul' or type == 'Div' or type == 'Mod':
        op = '+'
        if type == 'Sub':
            op = '-'
        if type == 'Mul':
            op = '*'
        if type == 'Div':
            op = 'div'
        if type == 'Mod':
            op = 'mod'
        RPN_tree.append(op)
        RPN_tree.append(preprocess(exp[1]))
        RPN_tree.append(preprocess(exp[2]))

    elif type == 'Read':
        arr_dict[exp[1][0]] = 1
        RPN_tree.append('select')
        RPN_tree.append(exp[1])
        RPN_tree.append(preprocess(exp[2]))

    elif type == 'BCmp' or type == 'ACmp':
        op = exp[1][2][0]
        if op != '!=':
            RPN_tree.append(op)
            RPN_tree.append(preprocess(exp[1][1]))
            RPN_tree.append(preprocess(exp[1][3]))
        else:
            RPN_tree = ['not', ['=', preprocess(exp[1][1]), preprocess(exp[1][3])]]

    elif type == 'BDisj' or type == 'BConj' or type == 'AAnd' or type == 'AOr' or type == 'AImply':
        op = '=>'
        if (type == 'BDisj' or type == 'AOr'):
            op = 'or'
        if (type == 'BConj' or type == 'AAnd'):
            op = 'and'
        RPN_tree.append(op)
        RPN_tree.append(preprocess(exp[1]))
        RPN_tree.append(preprocess(exp[2]))

    elif type == 'BNot' or type == 'ANot':
        RPN_tree.append('not')
        RPN_tree.append(preprocess(exp[1]))

    elif type == 'QUniv' or type == 'QExist':
        op = 'forall' if type == 'QUniv' else 'exists'
        varlist = [exp[1][1:len(exp[1])][0]]
        RPN_tree.append(op)
        RPN_tree.append(varlist)
        RPN_tree.append(preprocess(exp[2]))
    else:
        RPN_tree.append('true')

    return RPN_tree


# turn a program tree into a list of guarded commands
def convert_to_gc(tree):
    gc_list = []
    type = tree[0]

    if type == 'Root':
        pre = preprocess(tree[2])
        post = preprocess(tree[3])
        program = tree[4]
        gc_list = convert_to_gc(program)
        gc_list.append(['assert', post])
        gc_list.insert(0, ['assume', pre])

    elif type == 'List':
        for i in range(1, len(tree)):
            gc_list += convert_to_gc(tree[i])

    elif type == 'Assign':
        var = tree[1][0]
        var_dict[var] = 1
        tmp = get_var()
        exp = preprocess(tree[2])
        exp_new = replace_var(var, tmp, exp)
        gc_list.append(['assume', ['=', [tmp], [var]]])
        gc_list.append(['havoc', var])
        gc_list.append(['assume', ['=', [var], exp_new]])
        pass

    elif type == 'ParAssign':
        tmp = get_var()
        return convert_to_gc(['List',
                              ['Assign', [tmp], ['Var', tree[1]]],
                               ['Assign', tree[1], tree[3]],
                               ['Assign', tree[2], replace_var(tree[1][0], tmp, tree[4])]])

    elif type == 'Write':
        arr = tree[1][0]
        arr_dict[arr] = 1
        index = preprocess(tree[2])
        value = preprocess(tree[3])
        tmp = get_arr()
        ind_new = replace_var(arr, tmp, index)
        val_new = replace_var(arr, tmp, value)
        gc_list.append(['assume', ['=', [tmp], [arr]]])
        gc_list.append(['havoc', arr])
        gc_list.append(['assume', ['=', [arr], ['store', [tmp], ind_new, val_new]]])

    elif type == 'If':
        condition = preprocess(tree[1])
        branch1 = convert_to_gc(tree[2])
        branch2 = convert_to_gc(tree[3])
        gc_list.append(['box',[['assume',condition]] + branch1,
                              [['assume',['not',condition]]] + branch2])

    elif type == 'While':
        condition = preprocess(tree[1])
        invariant = preprocess(tree[2])
        havoc_list = find_vars(tree[3])
        loop_body = convert_to_gc(tree[3])
        gc_list.append(['assert', invariant])
        for i in range(len(havoc_list)):
            gc_list.append(['havoc', havoc_list[i]])
        gc_list.append(['assume', invariant])
        gc_list.append(['box',
                       [['assume',condition]]+loop_body+[['assert',invariant]]+[['assume',['false']]],
                       [['assume',['not',condition]]]])

    return gc_list


# compute the weakest precondition from a list of guarded commands
def compute_wp(gc_list, B):
    if len(gc_list) > 1:
        B = compute_wp(gc_list[:-1], compute_wp([gc_list[-1]],B))
    else:
        command = gc_list[0]
        if command[0] == 'box':
            B = ['and', compute_wp(command[1], B), compute_wp(command[2], B)]
        elif command[0] == 'assume':
            B = ['=>', command[1], B]
        elif command[0] == 'assert':
            B = ['and', command[1], B]
        elif command[0] == 'havoc':
            tmp = None
            if command[1] in var_dict:
                tmp = get_var()
            else:
                tmp = get_arr()
            B = replace_var(command[1], tmp, B)
    return B


# turn a weakest precondition tree into a z3-acceptable formula string
def format_as_z3(wp):
    if len(wp) == 1:
        return wp[0]
    arg1 = ''
    arg2 = ''
    if wp[0] == 'forall' or wp[0] == 'exists':
        arg1 = '('
        for i in range(len(wp[1])):
            arg1 += '(' + wp[1][i][0] + ' Int)'
        arg1 += ')'
        arg2 = format_as_z3(wp[2])
    elif wp[0] == 'not' or wp[0] == '!':
        arg1 = format_as_z3(wp[1])
    elif wp[0] == 'store':
        arg1 = format_as_z3(wp[1])
        arg2 = format_as_z3(wp[2]) + ' ' + format_as_z3(wp[3])
    else:
        arg1 = format_as_z3(wp[1])
        arg2 = format_as_z3(wp[2])
    return "(" + wp[0] + " " + arg1 + " " + arg2 + ")"


# ENTRY POINT
def main():

    # get the program string from the scala parser and preprocess it
    prog_string = sys.stdin.read()
    prog_string = "Root"+prog_string[prog_string.index('('):]
    prog_string = prog_string.replace(' ', '')

    # turn the program string given by the scala parser into a tree
    prog_tree = str_to_tree(prog_string)

    # convert the program tree into a list of guarded commands
    gc_list = convert_to_gc(prog_tree)

    # find the weakest precondition, formatted as a BST representing
    # a string in reverse polish notation
    weakest_pre = compute_wp(gc_list, ['true'])

    # prepare to send to z3

    # arrays
    arr_string = ''
    for arr_name in arr_dict:
        arr_string += "(declare-const " + arr_name + " (Array Int Int))"

    # variables
    var_string = ''
    for var_name in var_dict:
        var_string += "(declare-const " + var_name + " Int)"

    # header
    z3_input = "(define-fun program () Bool) (assert(not program)) (check-sat)"

    # format weakest precondition as z3 input
    z3_input = z3_input[0:27] + format_as_z3(weakest_pre) + z3_input[27:]
    z3_input = arr_string + var_string + z3_input

    # stdout is piped to z3
    print(z3_input)

if __name__ == "__main__":
    main()
