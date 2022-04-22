import copy
from operator import neg
from os import remove
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor
import sys
from utils import utils
from tools import MiniSAT
from circuit import Circuit
from run_bica import prime_cover_via_BICA

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

    def __init__ (self, str_formula, changeNegAlwaysEventually = True):
        self.changeNegAlwaysEventually = changeNegAlwaysEventually
        self.env_vars = set()
        self.sys_vars = set()
        self.ab = self.calculate_ab(str_formula)
        self.closure = calculate_closure(self.ab)
        for k,v in self.closure.items():
            print(k, v)
        print(calculate_separated_formulas(calculate_dnf(self.ab), dict()))


    def calculate_ab(self, str_formula):
        """
            Calculates binary tree of given str_formula
        """
        devStr = str_formula.replace("\t","").replace(" ", "").replace("\n","")
        ast = self.__parse_formula(devStr) #Formula as an ast tree
        ast_to_ab = self.visit(ast)
        nnf = self.__push_negs(ast_to_ab) #Push negs
        ab = self.__push_nexts(nnf) #Push Nexts
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
                return [NEXT_OPERATOR, children[1]]
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
                Next = "X"
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




def is_valid_model(model):   
    modelAux = list(model)
    while modelAux:
        l = modelAux.pop()
        if l[0] == "-" :
            lneg = l[1:]
        else:
            if is_always(l) or is_eventually(l):
                from temporal_formula import TemporalFormula
                lneg = TemporalFormula("-"+l).str
                
            else:
                lneg = "-" + l
        for lm in modelAux:
            if subsumes(lm, lneg):
                return False

    return True

def are_equal_formulas(sf1, sf2):
    """
        True: if two separated formulas sf1 and sf2 are equivalent
    """
    neg_sf1_ab = neg_separated_formulas_to_ab(sf1)
    neg_sf2__ab = neg_separated_formulas_to_ab(sf2)
    sf1_ab = separated_formulas_to_ab(sf1)
    sf2_ab = separated_formulas_to_ab(sf2)
    f1toAB = ['&', sf2_ab, neg_sf1_ab]
    f2toAB = ['&', sf1_ab, neg_sf2__ab]

    if not is_sat(f1toAB) or not is_sat(f2toAB):
        return False
    else:
        return True


def is_sat(formulaAB):
    "True if given formula is satisfiable"
    C = Circuit()
    C.list_to_circ(formulaAB)
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)
    is_sat = (MiniSAT("pos.cnf") == "SAT")
    remove("pos.cnf")
    return is_sat 


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
    limitInf = ""
    limitSup = ""
    start = False
    end = False
    cNext = get_number_nexts(formula)
    if is_atom(formula) or (formula[0] == "-" and is_atom(formula[1])):
        return int(0), int(0)
    if cNext > 0:
        return int(cNext), int(cNext)
    for f in formula[0]:

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

def neg_separated_formulas_to_ab(separated_formulas):
    """
         Return the negation of the given separated formulas 
    """
    neg_to_ab = ['&']
    for separated_formula in separated_formulas:
        neg_to_ab.append(neg_separated_formula_to_ab(separated_formula))
    return neg_to_ab


def neg_separated_formula_to_ab(separated_formula):
    """
         Return the negation of the given separated formula 
    """
    literals = separated_formula[0]
    futures = separated_formula[1]
    separated_formula_ab = ['|', 'False', 'False']
    for literal in literals:
        separated_formula_ab.append(simple_negation_ab(literal))
    neg_futures = ['&', 'True', 'True']
    for future in futures:
        neg_future_i = ['|', 'False', 'False']
        for f in future:
            neg_future_i.append(simple_negation_ab(f))
        neg_futures.append(neg_future_i)
    separated_formula_ab.append(neg_futures)

    return separated_formula_ab


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



def model_to_separated_formula(model, subsumptions):
    """
        Return a model in separated formula format
    """
    sf = empty_sf()
    
    for formula in list(model):
        futures = set()
        if "X" in formula or "F[" in formula or "G[" in formula:
            if not futures:
                futures.add(formula)
                continue
            delete_futures = set()
            for fi in list(futures):
                if subsumes(fi, formula, subsumptions):
                    break
                elif subsumes(formula, fi, subsumptions):
                    for fj in list(futures):
                        if subsumes(formula, fj, subsumptions):
                            delete_futures.add(fj)
                    
                    futures.add(formula)
                    break
                else:
                    futures.add(formula)
            futures = futures - delete_futures
                    
        else:
            if is_var_env(formula):
                sf['X'].add(formula)
            else:
                sf['Y'].add(formula)
    if futures == set():
            futures = {"True"}
    sf['Futures'].append(futures)
    return sf



def G_to_F(op):
    return op.replace(ALWAYS_OPERATOR, EVENTUALLY_OPERATOR)

def F_to_G(op):
    return op.replace(EVENTUALLY_OPERATOR, ALWAYS_OPERATOR)


def include_next_to_formula(formula):
    if formula[0] == 'G' or formula[0] =='F':
        formulaWithOutOp= formula.split("]")[1]
        limitInf, limitSup = get_temporal_op_limits(formula)
        newLimitInf = str(limitInf + 1)
        newLimitSup = str(limitSup + 1)
        return formula[0] + "[" +newLimitInf+","+newLimitSup+ "]"+formulaWithOutOp


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



def calculate_closure(formula):

    if is_binary(formula):
        f_neg = neg_formula_ab(formula)
        f_neg_str = to_str(f_neg)
        f_str = to_str(formula)
        c = {f_neg_str: f_str, f_str: f_neg_str}
        cl = calculate_closure(formula[1])
        cr = calculate_closure(formula[2])
        c.update(cl)
        c.update(cr)
        return c

    elif is_always(formula[0]) or is_eventually(formula[0]):
        neg_formula = neg_formula_ab(formula)
        neg_formula_not_change =  neg_formula_ab(formula, False)
        neg_formula_str = to_str(neg_formula)
        formula_str = to_str(formula)
        c = calculate_closure(formula[1])
        c.update({neg_formula_str: formula_str, formula_str: neg_formula_str, neg_formula_not_change: formula_str, formula_str: neg_formula_not_change})
        return c

    else:
        neg_formula = neg_formula_ab(formula)
        neg_formula_str = to_str(neg_formula)
        formula_str = to_str(formula)
        c =  {neg_formula_str: formula_str, formula_str: neg_formula_str}
        return c


def subsumes(future1, future2, subsumptions = None):
    #future1 subsumes future2
    if subsumptions:
        return future2 in subsumptions[future1]

    if future1 == future2:
        return True

    if future1[0] == "X":
        future1 = include_next_to_formula(future1[1:])

    if future2[0] == "X":
        future2 = include_next_to_formula(future2[1:])

    future1List = getStrToList(future1)
    future1Literals = get_literals(future1List)

    future2List = getStrToList(future2)

    future2Literals = get_literals(future2List)

    if future1Literals >= future2Literals and is_in_interval_success(future1List, future2List):
            if is_in_interval_success(future1List, future2List):
                literal1WithOutTemp = delete_temp_ops(future1List)
                literal2WithOutTemp = delete_temp_ops(future2List)
                f = ['&', literal1WithOutTemp, ['-', literal2WithOutTemp]]
                is_sat_f = is_sat(f)
                if not is_sat_f:
                    return True                    
    return False



def calculate_subsumptions(formula):
    subsumptions = dict()
    futures = set()
    for formula_i in formula:
        for formula_ij in formula_i:
            if "X" in formula_ij or "F[" in formula_ij or "G[" in formula_ij:
                subsumptions[formula_ij] = {formula_ij}
                futures.add(formula_ij)
    for key in subsumptions.keys():
        for future in list(futures):
            future1 = copy.deepcopy(key)
            future2 = copy.deepcopy(future)
            if subsumes(future1, future2):
                subsumptions[key].add(future)
    return subsumptions



def separated_formulas_to_ab(separated_formulas):
    to_ab = ['|']
    for separated_formula in separated_formulas:
        to_ab.append(separated_formula_to_ab(separated_formula))
    return to_ab

def separated_formula_to_ab(separated_formula):
    literals = separated_formula[0]
    futures = separated_formula[1]
    separated_formula_ab = ['&', 'True', 'True']
    for literal in literals:
        separated_formula_ab.append(simple_formula_ab(literal))
    neg_futures = ['|', 'False', 'False']
    for future in futures:
        neg_future_i = ['&', 'True', 'True']
        for f in future:
            neg_future_i.append(simple_formula_ab(f))
        neg_futures.append(neg_future_i)
    separated_formula_ab.append(neg_futures)
    return separated_formula_ab

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

def empty_sf():
    sf = dict()
    sf['X'] = set()
    sf['Y'] = set()
    sf['Futures'] = list()
    return sf

def calculate_dnf(ab):
    return prime_cover_via_BICA(ab)

def calculate_separated_formulas(dnf, subsumptions):
    processing_models = []
    for model in dnf:
        to_sf = model_to_separated_formula(model, subsumptions)
        processing_models.append(to_sf)
    return processing_models

ab1 = TemporalFormula("((~((((~controllable_5_s1 & ~controllable_5_s2 & ~controllable_5_s3 & variables_5_env_8_e) & ~(variables_5_env_13_e)) & ~(variables_5_env_12_e))) & X (((~controllable_5_s1 & ~controllable_5_s2 & ~controllable_5_s3 & variables_5_env_8_e) & (~(variables_5_env_13_e) & ~(variables_5_env_12_e))))) -> X (X (~controllable_5_s1 & ~controllable_5_s2 & controllable_5_s3)))")

p1 = ['G[0,4]', 'a']
p2 = ['G[0,1]', 'a']

print(is_in_interval_success(p1,p2))