import copy
import itertools
from operator import neg
import sys
import time
from traceback import print_tb
from tracemalloc import start
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor

from bica import prime_cover_via_BICA
from tools import add_info
from verifications import is_sat

NEG_OPERATORS = ["!", "-", "~"]
NEG_OPERATOR = "-"

AND_OPERATORS = ["&&", "&"]
AND_OPERATOR = "&"

OR_OPERATORS = ["||", "|"]
OR_OPERATOR = "|"


IMPLICATION_OPERATORS = ['->']

DOUBLE_IMPLICATION_OPERATORS = ['<-->']

NEXT_OPERATORS = ['X']
NEXT_OPERATOR = 'X'

EVENTUALLY_OPERATORS = ['F']
EVENTUALLY_OPERATOR = 'F'

ALWAYS_OPERATORS = ['G']
ALWAYS_OPERATOR = 'G'

TRUE_SYMBOLS = ['TRUE', 'T']
TRUE_SYMBOL = "True"

FALSE_SYMBOLS = ['FALSE', 'F']
FALSE_SYMBOL = 'False'


OPEN_PARENTHESIS_SYMBOL = "("


class TemporalFormula(NodeVisitor):

    """
        Temporal Formula is a formula in XNNF, that is, it follows the NNF but also include Evetually(limited) and next unary temporal operators.
        We represent the temporal fomula as a binary tree
    """

    def __init__ (self, formula, changeNegAlwaysEventually = True):
        self.info = dict()
        self.changeNegAlwaysEventually = changeNegAlwaysEventually
        sys.setrecursionlimit(10000)
        self.env_vars = set()
        self.ab = self.calculate_ab(formula)


    def calculate_ab(self, formula):
        """
            Calculates binary tree of given str_formula
        """
        start = time.time()
        ab = self.__calculate_ab(formula)
        add_info(self.info, "Calculate AB(s): ", time.time()-start)
        add_info(self.info, "Env vars(n): ", len(self.env_vars))
        return ab


    def __calculate_ab(self, formula):
        if isinstance(formula, str):
            devStr = formula.replace("\t","").replace(" ", "").replace("\n","")
            ast = self.__parse_formula(devStr) #Formula as an ast tree
            ast_to_ab = self.visit(ast)
            nnf = self.__push_negs(ast_to_ab) #Push negs
            ab = self.__push_nexts(nnf) #Push Nexts
            return ab
        elif len(formula) == 1:
            return self.calculate_ab(formula[0])
        else:

            ab = ['&']
            ab += [self.calculate_ab(str_formula) for str_formula in formula if str_formula != "\n" or str_formula != "" ]
            
            return ab

            



    def generic_visit(self, node, children):    

        if len(children) == 0:
            if is_var_env(node.text):
                self.env_vars.add(node.text)
            return node.text
        elif len(children) == 1:
            return children[0]
        elif len(children) == 2:
            if is_neg(children[0]):
                return [NEG_OPERATOR, children[1]]
            else:
                return [children[0], children[1]]
        elif children[0] == OPEN_PARENTHESIS_SYMBOL:
            return children[1]
        else:
            if children[1] in IMPLICATION_OPERATORS:
                return [OR_OPERATOR, [NEG_OPERATOR, children[0]], children[2]]
            elif children[1] in DOUBLE_IMPLICATION_OPERATORS:
                return [AND_OPERATOR, [OR_OPERATOR,[NEG_OPERATOR, children[0]],children[2]], [OR_OPERATOR,[NEG_OPERATOR, children[2]],children[0]]]
            else:
                if is_and(children[1]):
                    return [AND_OPERATOR, children[0], children[2]]
                else:
                    return [OR_OPERATOR, children[0], children[2]]



    def __next (self, formula, c):
        """
            Given a formula in ab representation and accumulation number of next (c), generate pushed next
        """
        if is_and(formula[0]):
            leftFormulaNext = self.__next(formula[1], c)
            rightFormulaNext = self.__next(formula[2], c)
            return [AND_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif is_or(formula[0]):
            leftFormulaNext = self.__next(formula[1], c)
            rightFormulaNext = self.__next(formula[2], c)
            return [OR_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif is_next(formula[0]):
            if len(formula[0]) > 1:
                c = get_next_n(formula[0])
            else:
                c +=1
            subformulaNext = self.__next(formula[1], c)
            return subformulaNext
        elif is_eventually(formula[0]):
            limitInf, limitSup =  get_temporal_op_limits(formula[0])
            subformulaXnnf = self.__push_nexts(formula[1])
            newOp = EVENTUALLY_OPERATOR + "[" + str(int(limitInf)+c) + "," + str(int(limitSup)+c) + "]"
            return [newOp, subformulaXnnf]
        elif is_always(formula[0]):
            limitInf, limitSup =  get_temporal_op_limits(formula[0])
            subformulaXnnf = self.__push_nexts(formula[1])
            newOp = ALWAYS_OPERATOR + "["+ str(int(limitInf)+c) + "," + str(int(limitSup)+c) + "]"
            return [newOp, subformulaXnnf]

        else:
            return self.__generar_next(formula, c)

    def __generar_next(self, formula, n):
        "Given a formula and a integer n generates equvalent next formula: formula = a, n = 5 generates X[5]a"
        return [NEXT_OPERATOR + "[" + str(n) + "]", formula]

    def __push_negs(self, formula):
        """
            Push negs to literals: -(a & c) returns (-a | -b)
        """
        if is_neg(formula[0]):
            if isinstance(formula[1], str) or (not self.changeNegAlwaysEventually and  is_eventually(formula[1][0])) or (not self.changeNegAlwaysEventually and  is_always(formula[1][0])):
                return formula
            formulaNeg = neg_formula_ab(formula[1], self.changeNegAlwaysEventually)
            return self.__push_negs(formulaNeg)
        elif is_unary(formula):
            rightFormulaNeg = self.__push_negs(formula[1])
            return [formula[0], rightFormulaNeg]
        elif is_binary(formula):
            leftFormulaNeg = self.__push_negs(formula[1])
            rightFormulaNeg = self.__push_negs(formula[2])
            return [formula[0],leftFormulaNeg, rightFormulaNeg]
            
        else:
            return formula
    
    def __push_nexts(self, formula):
        """
            Push nexts to literals: X(a & c) returns (Xa & Xb)
        """
        if is_neg(formula[0]):
            rightFormulaNext = self.__push_nexts(formula[1])
            return [NEG_OPERATOR, rightFormulaNext]
        elif is_and(formula[0]):
            leftFormulaNext = self.__push_nexts(formula[1])
            rightFormulaNext = self.__push_nexts(formula[2])
            return [AND_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif is_or(formula[0]):
            leftFormulaNext = self.__push_nexts(formula[1])
            rightFormulaNext = self.__push_nexts(formula[2])
            return [OR_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif is_next(formula[0]):
            if len(formula[0])>1:
                c = get_next_n(formula[0])
                rightFormulaNext = self.__next(formula[1], c)

            else:
                rightFormulaNext = self.__next(formula[1], 1)
            return rightFormulaNext
            
        else:
            return formula


    def __parse_formula(self, str):
            grammar = Grammar(
                """
                Bicondicional = (Condicional "<-->" Bicondicional) / Condicional
                Condicional = (Disyuncion "->" Condicional) / Disyuncion
                Disyuncion =  (Conjuncion ("||" / "|")  Disyuncion) / Conjuncion
                Conjuncion = (Literal ("&&"/"&") Conjuncion) / Literal
                Literal =  (Atomo) / ((Neg / Eventually / Next / Globally ) Literal)
                Atomo =  Var / Enum / Agrupacion
                Enum = (Var ("==" / "=") Var) / Var
                Agrupacion = ("(" Bicondicional ")") 
                Var = ~"[a-zA-EH-WY-Z0-9][a-zA-Z0-9_]*"
                Next = (~"X\[[0-9]+\]") / ("X")
                Eventually = ~"F\[[0-9]+\,[0-9]+\]" 
                Globally = ~"G\[[0-9]+\,[0-9]+\]"
                Neg = "!" / "-" / "~"
                """

            )
            """ try: 
                parse_formula = grammar.parse(str)
            except Exception as e:
                print(e)
                print("Fail parsing xnnf formula")
                print(str)
                parse_formula = None
                exit(0)
 """
            parse_formula = grammar.parse(str)
            return parse_formula

###### BOOLEAN  FUNCTIONS ######

def is_neg(op):
    return op in NEG_OPERATORS

def is_and(op):
    return op in AND_OPERATORS

def is_or(op):
    return op in OR_OPERATORS

def is_next(op):
    return (op in NEXT_OPERATOR) or (len(op) > 2 and op[0] in NEXT_OPERATORS and op[1] == "[")

def is_next_formula(formula):
    return is_neg(formula[0])

def is_eventually(op):
    return len(op) > 2 and op[0] in EVENTUALLY_OPERATORS and op[1] == "["

def is_always(op):
    return len(op) > 2 and op[0] in ALWAYS_OPERATORS and op[1] == "["

def is_var_env(var):
    return len(var) > 2 and var[-2:] == "_e" 

def is_true(formula):
    return isinstance(formula, str) and formula in TRUE_SYMBOLS

def is_false(formula):
    return isinstance(formula, str) and formula in FALSE_SYMBOLS

def is_unary(formula):
    return isinstance(formula, list) and len(formula) == 2

def is_binary(formula):
    return isinstance(formula, list) and len(formula) == 3
    
def is_variable(formula):
    return len(formula) == 1


def is_atom(strFormula):
    return get_variable(strFormula) == strFormula


def is_temp_op(op):
    return is_next(op) or is_always(op) or is_eventually(op)

def is_temp_formula(f):
    return is_next(f) or is_always(f) or is_eventually(f)

def has_neg(formula):
    return "-" in formula

def is_in_interval_success(phiAb, alphaAb):
    """
        TRUE: if phiAB interval subsumes alphaAb interval, ej G[0,4] subsumes G[0,1]
    """
    n, m = get_temporal_limits(alphaAb)
    nprima, mprima = get_temporal_limits(phiAb)
    if not is_always(phiAb[0]):
        if not is_always(alphaAb[0]):
            return (nprima >= n and nprima <= m) and (mprima >= n and mprima <= m)
        else:
            return n == m and mprima == nprima and n == nprima
    else:
       return (n >= nprima and nprima <= m) and (n <= mprima and mprima >= m)


################################



######### GET FUNCTIONS ########

def get_neg_literal(literal):
    first_char = literal[0]
    if first_char in NEG_OPERATORS:
        return literal[1:]
    else:
        return "-" + literal

def get_variable(literal):
    if literal[0] == "-":
        return literal[1:]
    else:
        return literal

def get_temporal_op_limits(op):
    limitInf = ""
    limitSup = ""
    start = False
    end = False
    for f in op:

        if f == ",":
            start = False
            end = True
        elif f == "]":
            break
        elif f == "[":
            start = True
        elif start:
            limitInf = limitInf + f
        elif end: 
            limitSup = limitSup + f
        else: 
            continue
    return int(limitInf), int(limitSup)

def get_temporal_limits(formula):
    if is_next(formula[0]):
        cNext = get_next_n(formula[0])
        return cNext, cNext
    elif is_eventually(formula[0]) or is_always(formula[0]):
        return get_temporal_op_limits(formula[0])
    else:
        return 0, 0

def get_number_nexts(formula):
    if is_next(formula[0]):
        return 1 +  get_number_nexts(formula[1])
    else:
        return 0

def getStrToList(formulaStr):
    return TemporalFormula(formulaStr).ab

def get_X(separated_formulas):
    X = set()
    for separated_formula in separated_formulas:
        for l in separated_formula[0]:
            if is_var_env(l):
                if l[0] == "-":
                    X.add(l[1:])
                else:
                    X.add(l)
    return X

def get_variable(formula):
    if is_temp_op(formula[0]):
        if is_eventually(formula):
            deleteEventuality = formula.split("]", 1)
            return get_variable(deleteEventuality[1])
        else:
            return get_variable(formula[1:])
    elif formula[0] == "-":
        return formula[1:]
    else :
        return formula

def get_literals(formula):
        if isinstance(formula, str):
            return {formula}
        elif len(formula) == 2:
            return get_literals(formula[1])
        else:
            res1 = get_literals(formula[1])
            res2 = get_literals(formula[2])
            return res1 | res2  


################################


######## NEG FUNCTIONS #########

def neg_formula_ab(formula, changeNegAlwaysEventually = True):
    """"
        Return formula negation
    """
    if isinstance(formula, str) and is_true(formula):
        return FALSE_SYMBOL
    elif isinstance(formula, str) and is_false(formula):
        return TRUE_SYMBOL
    elif is_neg(formula[0]):
        return formula[1]
    elif is_and(formula[0]):
        leftFormulaNeg = neg_formula_ab(formula[1])
        rightFormulaNeg = neg_formula_ab(formula[2])
        return [OR_OPERATOR,leftFormulaNeg, rightFormulaNeg]
    elif is_or(formula[0]):
        leftFormulaNeg = neg_formula_ab(formula[1])
        rightFormulaNeg = neg_formula_ab(formula[2])
        return [AND_OPERATOR,leftFormulaNeg, rightFormulaNeg]
    elif is_next(formula[0]):
        subformulaNeg = neg_formula_ab(formula[1])
        return [formula[0], subformulaNeg]
    elif is_eventually(formula[0]):
        subformulaNeg = neg_formula_ab(formula[1])
        if changeNegAlwaysEventually:
            return [F_to_G(formula[0]), subformulaNeg]
        else:
            return [NEG_OPERATOR, formula]

    elif is_always(formula[0]):
        subformulaNeg = neg_formula_ab(formula[1])
        if changeNegAlwaysEventually:
            return [G_to_F(formula[0]), subformulaNeg]
        else:
            return [NEG_OPERATOR, formula]
    else:
        return [NEG_OPERATOR, formula]
        

def neg_literal(strLiteral):
    """
        Return the negation of the given literal
    """
    if strLiteral[0] == "-":
        return strLiteral[1:]
    else:
        return "-" + strLiteral


def simple_negation_ab(l):
    if l == "True":
        return "False"
    if l == "False":
        return "True"
    if l[0] == "-":
        return l[1:]
    else:
        return ['-', l]

def simple_formula_ab(f):
    if f[0] == "-":
        return ['-', f[1:]]
    else:
        return f


################################


######## DELETE FUNCTIONS ######

def delete_neg_str(formula):
    return formula.replace("-", "")


def delete_temp_ops(formula):
    if is_temp_op(formula[0]):
        return delete_temp_ops(formula[1])
    else:
        return formula

################################



def G_to_F(op):
    return op.replace(ALWAYS_OPERATOR, EVENTUALLY_OPERATOR)

def F_to_G(op):
    return op.replace(EVENTUALLY_OPERATOR, ALWAYS_OPERATOR)

def get_next_n(next_op):
    n = ""
    start = False
    for c in next_op:
        if c == "[":
            start = True
            continue
        if c == "]":
            break
        if start:
            n += c
    return int(n)


def include_next_to_formula(formula):
    if is_always(formula[0]) or is_eventually(formula[0]):
        formulaWithOutOp= formula.split("]")[1]
        limitInf, limitSup = get_temporal_op_limits(formula)
        newLimitInf = str(limitInf + 1)
        newLimitSup = str(limitSup + 1)
        return formula[0] + "[" +newLimitInf+","+newLimitSup+ "]"+formulaWithOutOp

    elif is_next(formula[0]) and "[" in formula[0]:
        n = get_next_n(formula[0])
        return "X[" + str(n+1) + "]" + formula[1]
    else:
        return 'X(' + formula + ")" 

def to_str(formula):
    if isinstance(formula, str):
        return formula
    elif len(formula) == 2:
        if is_neg(formula[0]):
            return  formula[0] + to_str(formula[1])
        else:   
            return formula[0] + "(" + to_str(formula[1]) +")"
    else :
        leftFormula = to_str(formula[1])
        rightFormula = to_str(formula[2])
        return "(" + leftFormula + ")" + formula[0] + "(" + rightFormula + ")"


def dnf_to_sf(dnf, subsumptions, env_vars = False):
    sf = calculate_separated_formulas(dnf, subsumptions, env_vars)
    return sf

def get_all_dnf_temporal_formulas(dnf, info = dict()):
    res = set()
    for model in dnf:
        for f in model:
            if is_temp_formula(f):
                res.add(f)
    add_info(info, "DNF Temporal Formulas (n): ", len(res))
    return res

def calculate_subsumptions(set_formulas, info = dict()):
    start = time.time()
    subsumptions = dict()
    for formula1 in set_formulas:
        for formula2 in set_formulas:
            if formula1 == formula2:
                continue
            if subsumes(formula1, formula2):
                if formula1 not in subsumptions:
                    subsumptions[formula1] = set()
                subsumptions[formula1].add(formula2)
    add_info(info, "Subsumption(s)", time.time()-start)
    add_info(info, "Subsumption(n)", len(subsumptions))

    return subsumptions

def subsumes(future1, future2):
    #future1 subsumes future2

    if future1 == future2:
        return True

    #Cuidado revisar
    if future1[0] == "X" and future1[1] != "[":
        future1 = include_next_to_formula(future1[1:])

    if future2[0] == "X" and future2[1] != "[":
        future2 = include_next_to_formula(future2[1:])


    future1List = getStrToList(future1)
    future1Literals = get_literals(future1List)

    future2List = getStrToList(future2)
    future2Literals = get_literals(future2List)

    if future1Literals >= future2Literals:
            if is_in_interval_success(future1List, future2List):
                literal1WithOutTemp = delete_temp_ops(future1List)
                literal2WithOutTemp = delete_temp_ops(future2List)
                f = ['&', literal1WithOutTemp, ['-', literal2WithOutTemp]]
                is_sat_f = is_sat(f)
                if not is_sat_f:
                    return True                    
    return False




def print_subsumptions(s):
    for key in s.keys():
        print(" ", key, " subsumes ", s[key])



def model_to_separated_formula(model, subsumptions, sf_env_vars  = False):
    """
        Return a model in separated formula format
    """
    sf = empty_separated_formula()
    
    futures = set()
    for formula in list(model):
        if "X" in formula or "F[" in formula or "G[" in formula:
            #if not futures:
            futures.add(formula)
            continue
            # delete_futures = set()
            # for fi in list(futures):
            #     if subsumes(fi, formula, subsumptions):
            #         break
            #     elif subsumes(formula, fi, subsumptions):
            #         for fj in list(futures):
            #             if subsumes(formula, fj, subsumptions):
            #                 delete_futures.add(fj)
                    
            #         futures.add(formula)
            #         break
            #     else:
            #         futures.add(formula)
            # futures = futures - delete_futures
                    
        else:
            if is_var_env(formula):
                if sf_env_vars:
                    if get_variable(formula) in sf_env_vars:
                        sf['X'].add(formula)
                else:
                    sf['X'].add(formula)
            else:
                sf['Y'].add(formula)
    if not futures:
            futures = {"True"}
    sf['Futures'].append(futures)
    return sf

def calculate_separated_formulas(dnf, subsumptions, sf_env_vars = False):
    processing_models = []
    for model in dnf:
        to_sf = model_to_separated_formula(model, subsumptions, sf_env_vars)
        processing_models.append(to_sf)
    return processing_models


def empty_separated_formula():
    sf = dict()
    sf['X'] = set()
    sf['Y'] = set()
    sf['Futures'] = list()
    return sf 

def set_separated_formula(X, Y, F):
    sf = dict()
    sf['X'] = X
    sf['Y'] = Y
    sf['Futures'] = F
    return sf 

def are_equal_formulas(sf1, sf2):
    """
        True: if two separated formulas sf1 and sf2 are equivalent
    """
    
    neg_sf1_ab = neg_separated_formulas_to_ab(sf1)

    neg_sf2_ab = neg_separated_formulas_to_ab(sf2)
    

    sf1_ab = separated_formulas_to_ab(sf1)
    sf2_ab = separated_formulas_to_ab(sf2)

    f1toAB = ['&', sf2_ab, neg_sf1_ab]
    f2toAB = ['&', sf1_ab, neg_sf2_ab]


    if is_sat(f1toAB):
        return False
    elif is_sat(f2toAB):

        return False
    else:
        return True


def is_implicated(separted_formula_1, separted_formula_2):
    """
        1 -> 2, unsat, 1&-2
    """

    neg_separated_formula_2_ab = neg_separated_formulas_to_ab(separted_formula_2)
    separated_formula_1_ab = separated_formulas_to_ab(separted_formula_1)
    possible_tautology = ['&', separated_formula_1_ab, neg_separated_formula_2_ab]


    return not is_sat(possible_tautology)


def neg_separated_formulas_to_ab(separated_formulas):
    """
         Return the negation of the given separated formulas 
    """
    to_ab = ['&']
    for separated_formula in separated_formulas:
        separated_formula_ab = neg_separated_formula_to_ab(separated_formula)
        if separated_formula_ab:
            to_ab.append(separated_formula_ab)
    if len(to_ab) == 1:
        return list()
    elif len(to_ab) == 2:
        return to_ab[1]
    else:
        return to_ab


def neg_separated_formula_to_ab(separated_formula):
    """
         Return the negation of the given separated formula 
    """
    literals_sys = separated_formula['Y']
    literals_env = separated_formula['X']
    futures = separated_formula['Futures']

    separated_formula_ab = ['|']
    
    for literal in literals_env:
        separated_formula_ab.append(simple_negation_ab(literal))
    
    # for literal in literals_sys:
    #     separated_formula_ab.append(simple_negation_ab(literal))

    futures_ab = ['&']
    
    for future in futures:
        futures_i_ab = ['|']
        for f in future:
            futures_i_ab.append(simple_negation_ab(f))
    
        futures_i_ab = fix_ab_list(futures_i_ab)
        if futures_i_ab:  
            futures_ab.append(futures_i_ab)
    
    futures_ab = fix_ab_list(futures_ab)
    
    if futures_ab:
        separated_formula_ab.append(futures_ab)
    
    separated_formula_ab = fix_ab_list(separated_formula_ab)
    
    return separated_formula_ab


def separated_formulas_to_ab(separated_formulas):
    to_ab = ['|']
    for separated_formula in separated_formulas:
        separated_formula_ab = separated_formula_to_ab(separated_formula)
        if separated_formula_ab:
            to_ab.append(separated_formula_ab)
    if len(to_ab) == 1:
        return list()
    elif len(to_ab) == 2:
        return to_ab[1]
    else:
        return to_ab

def fix_ab_list(ab):
    if not ab:
        return list()
    if ab[0] in AND_OPERATORS + OR_OPERATORS:
        if len(ab) <= 1:
            return list()
        if len(ab) == 2:
            return ab[1]
        else:
            return ab

        

def separated_formula_to_ab(separated_formula):
    literals_sys = separated_formula['Y']
    literals_env = separated_formula['X']
    futures = separated_formula['Futures']

    separated_formula_ab = ['&']
    
    for literal in literals_env:
        separated_formula_ab.append(simple_formula_ab(literal))
    
    # for literal in literals_sys:
    #     separated_formula_ab.append(simple_formula_ab(literal))

    futures_ab = ['|']
    
    for future in futures:
        futures_i_ab = ['&']
        for f in future:
            futures_i_ab.append(simple_formula_ab(f))
    
        futures_i_ab = fix_ab_list(futures_i_ab)
        if futures_i_ab:  
            futures_ab.append(futures_i_ab)

    futures_ab = fix_ab_list(futures_ab)
    
    if futures_ab:
        separated_formula_ab.append(futures_ab)
    
    separated_formula_ab = fix_ab_list(separated_formula_ab)
    
    return separated_formula_ab

def print_separated_formula(formula, AND = " ∧ ", OR = " v "):

    res = ""
    for fi in formula:
        literal_fi = fi['X'] | fi['Y']
        futures_fi = fi['Futures']
        literals_str = ""
        for li_fi in list(literal_fi):
            if literals_str == "":
                literals_str += li_fi
            else:
                literals_str += AND +li_fi
        futures_str = ""
        for futuresi_fi in futures_fi:
            and_futures_ij = ""
            for futuresij_fi in futuresi_fi:
                if and_futures_ij == "":
                    and_futures_ij = futuresij_fi
                else:
                    and_futures_ij += AND +futuresij_fi

            if futures_str == "":
                futures_str = and_futures_ij
            else:
                futures_str = "(" + futures_str + ")" +  OR + "(" + and_futures_ij + ")"
        
        futures_str = "(" + futures_str + ")"
        
        if res == "":
            if literals_str ==  "":
                res += futures_str
            elif futures_str == "":
                res += "(" + literals_str  + ")"
            else:
                res += "(" + literals_str + AND + futures_str + ")"
        else:
            if literals_str ==  "":
                res += OR + "(" + futures_str + ")"
            elif futures_str == "":
                res += OR + "(" + literals_str  + ")"
            else:
                res += OR + "(" + literals_str + AND + futures_str + ")"
        res += "\n"
        
    print(res)
    return res

def get_env_variables(separated_formulas):
    env_vars = set()
    for sf in separated_formulas:
        for literal in sf['X']:
            var = get_variable(literal)
            env_vars.add(var)
    return env_vars

def get_all_assignments(var_set):
    l = [False, True]
    n = len(var_set)
    var_list = list(var_set)
    assignments = list(itertools.product(l, repeat=n)) 
    assignmentsList = list()
    for assignment in assignments:
        assignmentSet = set()
        for i in range(0, n):
            if assignment[i]:
                assignmentSet.add(var_list[i])
            else:
                assignmentSet.add("-"+var_list[i])
        assignmentsList.append(assignmentSet)
    return assignmentsList

    


def weakest_sf(self, separated_formulas):
    res = list()
    for sf_i in separated_formulas:
        sf_i_env_literals = self.__delete_system_vars(sf_i[0])
        sf_i_futures = sf_i[1]

        added = False
        for sf_j in res:
            sf_j_env_literals = sf_j[0]
            sf_j_futures = sf_j[1]
            if sf_i_env_literals <= sf_j_env_literals and self.are_all_futures_in(sf_j_futures, sf_i_futures):
                res.remove(sf_j)
                res.append([sf_i_env_literals, sf_i_futures])
                added = True
                break
            if sf_j_env_literals <= sf_i_env_literals and self.are_all_futures_in(sf_i_futures, sf_j_futures):
                added = True
                break
        if not added:
            res.append([sf_i_env_literals, sf_i_futures])
    return res

def dnf_to_separated_formulas(models, subsumptions):    
    processing_models = []
    for model in models:
        literals = set()
        futures = set()
        for l in list(model):
            if "X" in l or "F[" in l or "G[" in l:
                if not futures:
                    futures.add(l)
                    continue
                delete_futures = set()
                for fi in list(futures):
                    if subsumes(fi, l, subsumptions):
                        break
                    elif subsumes(l, fi, subsumptions):
                        for fj in list(futures):
                            if subsumes(l, fj, subsumptions):
                                delete_futures.add(fj)
                        
                        futures.add(l)
                        break
                    else:
                        futures.add(l)
                futures = futures - delete_futures
                       
            else:
                literals.add(l)
        if futures == set():
            futures = {"True"}
        processing_models.append([literals, [futures]])
    return processing_models

def calculate_dnf(formula, info = dict()):
    start = time.time()
    if formula == 'True':
        return list()
    if len(formula) < 3:
        formula = ['&', formula, formula]
    dnf = prime_cover_via_BICA(formula)
    add_info(info, "DNF(s): ", time.time()-start)
    add_info(info, "DNF(n): ", len(dnf))


    return dnf
