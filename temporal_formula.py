import sys
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor

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
        self.changeNegAlwaysEventually = changeNegAlwaysEventually
        sys.setrecursionlimit(10000)
        self.env_vars = set()
        self.ab = self.calculate_ab(formula)


    def calculate_ab(self, formula):
        """
            Calculates binary tree of given str_formula
        """
        if isinstance(formula, str):
            devStr = formula.replace("\t","").replace(" ", "").replace("\n","")
            ast = self.__parse_formula(devStr) #Formula as an ast tree
            ast_to_ab = self.visit(ast)
            nnf = self.__push_negs(ast_to_ab) #Push negs
            ab = self.__push_nexts(nnf) #Push Nexts
            return ab
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
                Next = ~"X\[[0-9]+\]" / "X"
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
    for c in next_op:
        if c == "[":
            start = True
        if c == "]":
            start = False
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
