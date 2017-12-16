from collections import defaultdict, Sequence
from copy import deepcopy
import itertools

class FOLogic_KB():
    def __init__(self, sentences = None):
        self.sentences = []
        self.index = dict()
        if sentences!=None:
            for logic in sentences:
                self.tell_logic(logic)

    def tell_logic(self, logic):
        self.sentences.append(logic)
        for predicate in set(get_predicates(logic)):
            self.indexing(predicate, len(self.sentences) - 1)

    def indexing(self, predicate, index):
        if predicate in self.index:
            self.index[predicate].add(index)
        else:
            self.index[predicate] = set()
            self.index[predicate].add(index)

    def predicate_matching(self, predicate):
        sentences = []
        if predicate in self.index:
            for inx in self.index[predicate]:
                sentences.append(self.sentences[inx]) 
        return set(sentences)

    def resolving_sentences(self, logic):
        logic_resolve = set()
        for predicate in get_predicates(logic):
            if predicate[0] == "~":
                predicate = predicate[1:]
            else:
                predicate = "~" + predicate
            logic_resolve = logic_resolve.union(self.predicate_matching(predicate))
        return logic_resolve

    def ask(self, logic):
        return query_resolution(self, logic)

class FOLogic():
    def __init__(self, operator, *arguments):
        self.operator = operator
        self.arguments = arguments

    def __invert__(self):
        return FOLogic("~", self)

    def __or__(self, rhs):
        if isinstance(rhs, FOLogic):
            return FOLogic("|", self, rhs)
        else:
            return ParFOLogic(rhs, self)

    def __ror__(self, lhs):
        return FOLogic("|", lhs, self)

    def __eq__(self, other):
        return (isinstance(other, FOLogic) and self.operator == other.operator and self.arguments == other.arguments)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.operator) ^ hash(self.arguments)

    def __repr__(self):
        arguments = [str(operand) for operand in self.arguments]
        if (isinstance(self.operator, str) and self.operator[0].isalpha()):
            return '{}({})'.format(self.operator, ', '.join(arguments)) if arguments else self.operator
        elif len(arguments) == 1:
            return self.operator + arguments[0]
        else:
            return "(" + (" " + str(self.operator) + " ").join(arguments) + ")"

    def __call__(self, *arguments):
        return FOLogic(self.operator, arguments)

class ParFOLogic():
    def __init__(self, operator, lhs):
        self.operator = operator
        self.lhs = lhs

    def __or__(self, rhs):
        return FOLogic(self.operator, self.lhs, rhs)

    def __repr__(self):
        return "ParFOLogic('{}', {})".format(self.operator, self.lhs)

class logic_namespace(defaultdict):
    def __missing__(self, key):
        self[key] = result = self.default_factory(key)
        return result

def create_const(constant):
    return FOLogic(constant)

def del_element(item, seq):
    result = []
    for x in seq:
        if x != item:
            result.append(x)
    return result

def get_predicates(sentence, negated = False):
    predicates = []
    if isinstance(sentence, FOLogic):
        if isinstance(sentence.operator, str) and sentence.operator.isalpha() and sentence.operator[0].isupper() and len(sentence.arguments) >= 1:
            predicates.append(sentence.operator if not negated else "~" + sentence.operator)
        else:
            for operand in sentence.arguments:
                if sentence.operator == "~":
                    res = True
                else:
                    res = False
                predicates += get_predicates(operand, res)
    return predicates

def get_phrases(arguments, operator):
    oper = []
    for operand in arguments:
        if operand.operator == operator:
            oper += get_phrases(operand.arguments, operator)
        else:
            oper.append(operand)
    return oper

def associate(arguments, operator):
    length = len(arguments)
    if length == 0:
        return False
    if length == 1:
        return arguments[0]
    else:
        return FOLogic(operator, *arguments)

def redundancy_check(x):
    n = len(x)
    x = list(x)
    y = []
    list1 = []
    for i in range(0, n):
        y.append(set(get_phrases([x[i]], "|")))
    for i in range(0, n):
        p = set(get_phrases([x[i]], "|"))
        for j in range(i + 1, n):
            if p == y[j]:
                list1.append(i)
    list2 = sorted(set(list1), reverse=True)
    for index in list2:
        del x[index]
    return set(x)

def substitute(s, x):
    if isinstance(x, list):
        return [substitute(s, xi) for xi in x]
    elif isinstance(x, tuple):
        return tuple([substitute(s, xi) for xi in x])
    elif not isinstance(x, FOLogic):
        return x
    elif ((isinstance(x.operator, str) and x.operator[0].isalpha()) and x.operator[0].islower()):
        return s.get(x, x)
    else:
        return FOLogic(x.operator, *[substitute(s, arg) for arg in x.arguments])

def unify_variables(var, x, theta):
    if var in theta:
        return unification(theta[var], x, theta)
    else:
        substitution = deepcopy(theta)
        substitution[var] = x
        return substitution

def unification(x, y, theta):
    if theta is None:
        return None
    elif x == y:
        return theta
    elif (isinstance(x, FOLogic) and not x.arguments and x.operator[0].islower()):
        return unify_variables(x, y, theta)
    elif (isinstance(y, FOLogic) and not y.arguments and y.operator[0].islower()):
        return unify_variables(y, x, theta)
    elif isinstance(x, FOLogic) and isinstance(y, FOLogic):
        return unification(x.arguments, y.arguments, unification(x.operator, y.operator, theta))
    elif isinstance(x, Sequence) and isinstance(y, Sequence):
        if len(x) == len(y) and not isinstance(x, str) and not isinstance(y, str):
            return unification(x[1:], y[1:], unification(x[0], y[0], theta))
        else:
            return None
    else:
        return None

def resolve(ci, cj):
    new_clauses = []
    clause1_disjuncts = get_phrases([ci], "|")
    clause2_disjuncts = get_phrases([cj], "|")
    for disjunct1 in clause1_disjuncts:
        for disjunct2 in clause2_disjuncts:
            subst = dict()
            if disjunct1.operator == "~":
                subst = unification(disjunct1.arguments[0], disjunct2, subst)
            elif disjunct2.operator == "~":
                subst = unification(disjunct1, disjunct2.arguments[0], subst)
            if subst is not None:
                disjunct1 = substitute(subst, disjunct1)
                disjunct2 = substitute(subst, disjunct2)
                if disjunct1 == ~disjunct2 or ~disjunct1 == disjunct2:
                    clause1_disjuncts = substitute(subst, clause1_disjuncts)
                    clause2_disjuncts = substitute(subst, clause2_disjuncts)
                    dnew = list(set(del_element(disjunct1, clause1_disjuncts) + del_element(disjunct2, clause2_disjuncts)))
                    new_clauses.append(associate(dnew, "|"))
    return new_clauses

def query_resolution(KB, query):
    clauses = KB.sentences + [~standardization(parse_logic(query))]
    NewKB = FOLogic_KB(clauses)
    new = set()
    while True:
        logic_pairs = []
        n = len(NewKB.sentences)
        for i in range(n):
            sentences_that_resolve = NewKB.resolving_sentences(NewKB.sentences[i])
            for j in range(i+1,n):
                if NewKB.sentences[j] in sentences_that_resolve:
                    logic_pairs.append((NewKB.sentences[i], NewKB.sentences[j]))
        for (clause1, clause2) in logic_pairs:
            resolvents = resolve(clause1, clause2)
            if False in resolvents:
                return True
            new = new.union(set(resolvents))
        new = redundancy_check(new)
        if new.issubset(set(NewKB.sentences)):
            return False
        if len(new) > 3000:
            return False
        for c in new:
            if c not in NewKB.sentences:
                NewKB.tell_logic(c)

def standardization(logic, dic=None):
    if dic is None:
        dic = {}
    if not isinstance(logic, FOLogic):
        if isinstance(logic, tuple):
            return tuple(standardization(operand, dic) for operand in logic)
        else:
            return logic
    elif isinstance(logic.operator, str) and logic.operator[0].isalpha() and logic.operator[0].islower():
        if logic in dic:
            return dic[logic]
        else:
            v = FOLogic('v_{}'.format(next(standardization.counter)))
            dic[logic] = v
            return v
    else:
        return FOLogic(logic.operator,*[standardization(a, dic) for a in logic.arguments])

standardization.counter = itertools.count()

def parse_logic(logic):
    if isinstance(logic, str):
        logic = logic.replace("=>", "|" + repr("=>") + "|")
        return eval(logic, logic_namespace(create_const))

def getinput():
    fname = 'input.txt'
    lines = [line.rstrip('\n') for line in open(fname)]
    no_of_queries = int(lines[0])
    return no_of_queries, lines[1:1+no_of_queries], int(lines[1+no_of_queries]), lines[2+no_of_queries:len(lines)]

def writeresult(results):
    f = open('output.txt','w')
    for i  in range(0,len(results)):
        res = str(results[i]) + "\n"
        f.write(res)
    f.close

def prepareKB(KB, kbHash):
    for i in range(0,len(kbHash)):
        kb_sentence = kbHash[i].replace(" ","")
        KB.tell_logic(standardization(parse_logic(kb_sentence)))
    return KB

def main():
    no_of_queries, queries, kbsize, kbHash = getinput()
    results = []

    KB = FOLogic_KB()
    KB = prepareKB(KB, kbHash)

    for query in queries:
        decision = KB.ask(query)
        result = 'TRUE' if (decision == True) else 'FALSE'
        results.append(result)

    writeresult(results)

if __name__ == '__main__':
    main()
