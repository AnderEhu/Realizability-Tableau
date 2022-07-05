import copy
import itertools
from posixpath import split
import sys
import time
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor

from bica import prime_cover_via_BICA
from circuit import Circuit
from tools import MiniSAT, add_info, analysis, correct_bica_formula

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

TRUE_SYMBOLS = ['TRUE', 'True', 'T']
TRUE_SYMBOL = "True"

FALSE_SYMBOLS = ['FALSE', 'False', 'F']
FALSE_SYMBOL = 'False'


OPEN_PARENTHESIS_SYMBOL = "("

AUX_NODE = "aux_var"
NEG_AUX_NODE = [NEG_OPERATOR,  "aux_var"]






class TemporalFormula(NodeVisitor):

    """
        Temporal Formula is a formula in XNNF, that is, it follows the NNF but also include Evetually(limited) and next unary temporal operators.
        We represent the temporal fomula as a binary tree
    """
    def __init__ (self, formula, 
            changeNegAlwaysEventually = False,
            extract_negs_from_nexts = True, 
            split_futures = False, 
            strict_future_formulas = False,
            **kwargs):

        sys.setrecursionlimit(10000)
        self.info = dict()
        self.split_futures = split_futures
        self.changeNegAlwaysEventually = changeNegAlwaysEventually
        self.extract_negs_from_nexts = extract_negs_from_nexts
        self.env_vars = set()
        self.strict_future_formulas = strict_future_formulas
       
        self.ab = self.calculate_ab(formula, **kwargs)
    

    
    @analysis    
    def calculate_ab(self, formula, **kwargs):
        """
            Calculates binary tree of given str_formula
        """
        ab = self.__calculate_ab(formula, **kwargs)
        return ab
    
    def __calculate_ab(self, formula, **kwargs):
        if isinstance(formula, str):
            devStr = formula.replace("\t","").replace(" ", "").replace("\n","")
            ast = self.__parse_formula(devStr, **kwargs) #Formula as an ast tree
            ast_to_ab = self.visit(ast)
            ab_next_pushed =  TemporalFormula.push_nexts(ast_to_ab, **kwargs)
            ab = TemporalFormula.push_negs(ab_next_pushed, self.changeNegAlwaysEventually, **kwargs)
            if self.extract_negs_from_nexts:
                ab = TemporalFormula.extract_neg_from_nexts(ab, **kwargs)
            return ab
        elif len(formula) == 1:
            return self.calculate_ab(formula[0], **kwargs)
        else:

            ab = ['&']
            ab += [self.calculate_ab(str_formula, **kwargs) for str_formula in formula if str_formula != "\n" or str_formula != "" ]
            
            return ab

    def generic_visit(self, node, children):    

        if len(children) == 0:
            return self.__general_visit_atom(node)
        elif len(children) == 1:
            return children[0]
        elif len(children) == 2:
            if TemporalFormula.is_neg(children[0]):
                return [NEG_OPERATOR, children[1]]
            elif TemporalFormula.is_next(children[0]):
                return [children[0], children[1]]
            elif TemporalFormula.is_always(children[0]):
                return self.__general_visit_always(children)
            else:
                assert TemporalFormula.is_eventually(children[0])
                return self.__general_visit_eventually(children)
        elif len(children) == 3 and TemporalFormula.is_and(children[1]):
            return [AND_OPERATOR, children[0], children[2]]
        elif len(children) == 3 and TemporalFormula.is_or(children[1]):
            return [OR_OPERATOR, children[0], children[2]]
        elif len(children) == 3 and children[1] in IMPLICATION_OPERATORS:
            return [OR_OPERATOR, [NEG_OPERATOR, children[0]], children[2]]
        elif len(children) == 3 and children[1] in DOUBLE_IMPLICATION_OPERATORS:
            return [AND_OPERATOR, [OR_OPERATOR,[NEG_OPERATOR, children[0]],children[2]], [OR_OPERATOR,[NEG_OPERATOR, children[2]],children[0]]]
        else:
            assert children[0] == OPEN_PARENTHESIS_SYMBOL
            return children[1]

    def __general_visit_atom(self, node):
        if node.text in TRUE_SYMBOLS:
            return [OR_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        elif node.text in FALSE_SYMBOLS:
            return [AND_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        else:
            return node.text
    def __general_visit_eventually(self, children):
        return self.__general_visit_always_or_eventually(children, EVENTUALLY_OPERATOR)
    def __general_visit_always(self, children):
        return self.__general_visit_always_or_eventually(children, ALWAYS_OPERATOR)
    def __general_visit_always_or_eventually(self, children, op):
        #Codigo repetido (revisar)
        if self.split_futures:
            limitInf, limitSup = TemporalFormula.get_temporal_op_limits(children[0])
            if limitInf == limitSup:
                return TemporalFormula.generate_next(children[1], limitInf, self.extract_negs_from_nexts)
            new_limit_sup = limitSup-1
            left_children = TemporalFormula.generate_next(children[1], limitInf, self.extract_negs_from_nexts)
            if limitInf == new_limit_sup:
                right_children = TemporalFormula.generate_next(children[1], limitInf+1, self.extract_negs_from_nexts)
            else:
                limitsSupMinus1 = op + "[" + str(limitInf) +  "," + str(new_limit_sup) + "]"
                right_children = ['X[1]', [limitsSupMinus1, children[1]]]
            if op == "G":
                return [AND_OPERATOR, left_children, right_children]
            else:
                return [OR_OPERATOR, left_children, right_children]
        elif self.strict_future_formulas:
            limitInf, limitSup = TemporalFormula.get_temporal_op_limits(children[0])
            if limitInf > 0:
                return [children[0], children[1]]
            else:
                if limitInf == limitSup:
                    return TemporalFormula.generate_next(children[1], limitInf, self.extract_negs_from_nexts)
                new_limit_sup = limitSup-1
                left_children = TemporalFormula.generate_next(children[1], limitInf, self.extract_negs_from_nexts)
                if limitInf == new_limit_sup:
                    right_children = TemporalFormula.generate_next(children[1], limitInf+1, self.extract_negs_from_nexts)
                else:
                    limitsSupMinus1 = op + "[" + str(limitInf) +  "," + str(new_limit_sup) + "]"
                    right_children = ['X[1]', [limitsSupMinus1, children[1]]]
                if op == "G":
                    return [AND_OPERATOR, left_children, right_children]
                else:
                    return [OR_OPERATOR, left_children, right_children]


        else:
            return [children[0], children[1]]

    @analysis
    def __parse_formula(self, str, **kwargs):
            grammar = Grammar(
                """
                Bicondicional = (Condicional "<-->" Bicondicional) / Condicional
                Condicional = (Disyuncion "->" Condicional) / Disyuncion
                Disyuncion =  (Conjuncion ("||" / "|")  Disyuncion) / Conjuncion
                Conjuncion = (Literal ("&&"/"&") Conjuncion) / Literal
                Literal =  (Atomo) / ((Neg / Eventually / Next / Globally ) Literal)
                Atomo = True / False /  Var / Agrupacion
                Agrupacion = ("(" Bicondicional ")") 
                Var = (~"[a-zA-EH-WY-Z0-9][a-zA-Z0-9_]*")
                Next = ~"X\[[0-9]+\]" / "X"
                Eventually = ~"F\[[0-9]+\,[0-9]+\]" 
                Globally = ~"G\[[0-9]+\,[0-9]+\]"
                Neg = "!" / "-" / "~"
                True = "TRUE" / "True"
                False = "FALSE" / "False"
                """

            )
            try: 
                parse_formula = grammar.parse(str)
            except Exception as e:
                print(e)
                print("Fail parsing xnnf formula")
                print(str)
                parse_formula = None
                exit(0)

            return parse_formula

    @staticmethod
    @analysis
    def next(formula, c, **kwargs):
        """
            Given a formula in ab representation and accumulation number of next (c), generate pushed next
        """
        if TemporalFormula.is_and(formula[0], **kwargs):
            leftFormulaNext = TemporalFormula.next(formula[1], c, **kwargs)
            rightFormulaNext = TemporalFormula.next(formula[2], c, **kwargs)
            return [AND_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif TemporalFormula.is_or(formula[0], **kwargs):
            leftFormulaNext = TemporalFormula.next(formula[1], c, **kwargs)
            rightFormulaNext = TemporalFormula.next(formula[2], c, **kwargs)
            return [OR_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif TemporalFormula.is_next(formula[0], **kwargs):
            if len(formula[0]) > 1:
                c += TemporalFormula.get_next_n(formula[0], **kwargs)
            else:
                c +=1
            subformulaNext = TemporalFormula.next(formula[1], c, **kwargs)
            return subformulaNext
        elif  TemporalFormula.is_neg(formula[0], **kwargs):
            return [NEG_OPERATOR, TemporalFormula.next(formula[1], c, **kwargs)]
        else:
            return TemporalFormula.generate_next(formula, c, **kwargs)

    @staticmethod
    @analysis
    def generate_next(formula, n, extract_negs_from_nexts = False, **kwargs):
        "Given a formula and a integer n generates equvalent next formula: formula = a, n = 5 generates X[5]a"
        if n == 0:
            return formula
        else:
            if TemporalFormula.is_neg(formula[0], **kwargs) and  extract_negs_from_nexts:
                return ['-', [NEXT_OPERATOR + "[" + str(n) + "]", formula[1]]]
            else:
                return [NEXT_OPERATOR + "[" + str(n) + "]", formula]

    @staticmethod
    @analysis
    def push_negs(formula, changeNegAlwaysEventually = False, **kwargs):
        """
            Push negs to literals: -(a & c) returns (-a | -b)
        """
        if TemporalFormula.is_neg(formula[0], **kwargs):
            if isinstance(formula[1], str) or (not changeNegAlwaysEventually and  (TemporalFormula.is_eventually(formula[1][0], **kwargs) or  TemporalFormula.is_always(formula[1][0], **kwargs))):
                return formula
            else:
                formulaNeg = TemporalFormula.neg_formula_ab(formula[1], changeNegAlwaysEventually, **kwargs)
                return TemporalFormula.push_negs(formulaNeg, **kwargs)
        elif TemporalFormula.is_binary(formula, **kwargs):
            leftFormulaNeg = TemporalFormula.push_negs(formula[1], **kwargs)
            rightFormulaNeg = TemporalFormula.push_negs(formula[2], **kwargs)
            return [formula[0],leftFormulaNeg, rightFormulaNeg]
            
        else:
            return formula

    @staticmethod
    @analysis
    def push_nexts(formula, **kwargs):
        """
            Push nexts to literals: X(a & c) returns (Xa & Xb)
        """
        if TemporalFormula.is_neg(formula[0], **kwargs):
            rightFormulaNext = TemporalFormula.push_nexts(formula[1], **kwargs)
            return [NEG_OPERATOR, rightFormulaNext]
        elif TemporalFormula.is_and(formula[0], **kwargs):
            leftFormulaNext = TemporalFormula.push_nexts(formula[1], **kwargs)
            rightFormulaNext = TemporalFormula.push_nexts(formula[2], **kwargs)
            return [AND_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif TemporalFormula.is_or(formula[0], **kwargs):
            leftFormulaNext = TemporalFormula.push_nexts(formula[1], **kwargs)
            rightFormulaNext = TemporalFormula.push_nexts(formula[2], **kwargs)
            return [OR_OPERATOR,leftFormulaNext, rightFormulaNext]

        elif TemporalFormula.is_next(formula[0], **kwargs):
            if len(formula[0])>1:
                c = TemporalFormula.get_next_n(formula[0], **kwargs)
                rightFormulaNext = TemporalFormula.next(formula[1], c, **kwargs)

            else:
                rightFormulaNext = TemporalFormula.next(formula[1], 1, **kwargs)
            return rightFormulaNext
            
        else:
            return formula

    ###### BOOLEAN  FUNCTIONS ######
    @staticmethod
    @analysis
    def is_neg(op, **kwargs):
        return isinstance(op, str) and op in NEG_OPERATORS

    @staticmethod
    @analysis
    def is_and(op, **kwargs):
        return isinstance(op, str) and op in AND_OPERATORS

    @staticmethod
    @analysis
    def is_or(op, **kwargs):
        return isinstance(op, str) and op in OR_OPERATORS

    @staticmethod
    @analysis
    def is_next(op, **kwargs):
        return isinstance(op, str) and ((op in NEXT_OPERATOR) or (len(op) > 3 and op[0] in NEXT_OPERATORS and op[1] == "["))

    @staticmethod
    @analysis
    def is_next_formula(formula, **kwargs):
        return TemporalFormula.is_next(formula[0])
    
    @staticmethod
    @analysis
    def is_eventually(op, **kwargs):
        return isinstance(op, str) and  len(op) > 5 and op[0] in EVENTUALLY_OPERATORS and op[1] == "["
    
    @staticmethod
    @analysis
    def is_always(op, **kwargs):
        return isinstance(op, str) and  len(op) > 5 and op[0] in ALWAYS_OPERATORS and op[1] == "["
    
    @staticmethod
    @analysis
    def is_var_env(var, **kwargs):
        return len(var) > 2 and var[-2:] == "_e" 
    
    @staticmethod
    @analysis
    def is_true(formula, **kwargs):
        return isinstance(formula, str) and formula in TRUE_SYMBOLS
    
    @staticmethod
    @analysis
    def is_false(formula, **kwargs):
        return isinstance(formula, str) and formula in FALSE_SYMBOLS
    
    @staticmethod
    @analysis
    def is_unary(formula, **kwargs):
        return isinstance(formula, list) and len(formula) == 2
    
    @staticmethod
    @analysis
    def is_binary(formula, **kwargs):
        return isinstance(formula, list) and len(formula) >= 3
    
    @staticmethod
    @analysis
    def is_atom(strFormula, **kwargs):
        return isinstance(strFormula, str) and TemporalFormula.get_variable(strFormula, **kwargs) == strFormula
    
    @staticmethod
    @analysis
    def is_temp_op(op, **kwargs):
        return isinstance(op, str) and (TemporalFormula.is_next(op, **kwargs) or TemporalFormula.is_always(op, **kwargs) or TemporalFormula.is_eventually(op, **kwargs))
    
    @staticmethod
    @analysis
    def is_temp_formula(formula, **kwargs):
        return isinstance(formula, list) and TemporalFormula.is_temp_op(formula[0], **kwargs)
    
    @staticmethod
    @analysis 
    def is_in_interval_success(phiAb, alphaAb, **kwargs):
        """
            TRUE: if phiAB interval subsumes alphaAb interval, ej G[0,4] subsumes G[0,1]
        """
        n, m = TemporalFormula.get_temporal_limits(alphaAb, **kwargs)
        nprima, mprima = TemporalFormula.get_temporal_limits(phiAb, **kwargs)
        if not TemporalFormula.is_always(phiAb[0], **kwargs):
            if not TemporalFormula.is_always(alphaAb[0], **kwargs):
                return (nprima >= n and nprima <= m) and (mprima >= n and mprima <= m)
            else:
                return n == m and mprima == nprima and n == nprima
        else:
            return (n >= nprima and nprima <= m) and (n <= mprima and mprima >= m)


    @staticmethod
    @analysis
    def is_implicated(formula_1_ab, formula_2_ab, **kwargs):
        """
            1 -> 2, unsat, 1&-2
        """

        neg_formula_2_ab = TemporalFormula.neg_formula_ab(formula_2_ab, changeNegAlwaysEventually=False, **kwargs)
        possible_contradiction = ['&', formula_1_ab, neg_formula_2_ab]

        prime_implicants = prime_cover_via_BICA(possible_contradiction)
        fix_prime_implacants = TemporalFormula.fix_prime_implicants_bica(prime_implicants)
        if not fix_prime_implacants:
            return True
        else:
            #print("VALID: ", prime_implicants)
            return False

    def is_implicated_strict_formulas(strict_formula_1_ab, strict_formula_2_ab, **kwargs):
        """
            1 -> 2, unsat, 1&-2
        """

        neg_strict_formula_2_ab = TemporalFormula.neg_strict_futures_from_safety_formula(strict_formula_2_ab, **kwargs)
        ##print(strict_formula_2_ab, " NEG ===>", neg_strict_formula_2_ab, "\n")
        possible_contradiction = ['&', strict_formula_1_ab, neg_strict_formula_2_ab]

        prime_implicants = prime_cover_via_BICA(possible_contradiction)
        #print("Prime ", prime_implicants, "\n")
        fix_prime_implacants = TemporalFormula.fix_prime_implicants_bica(prime_implicants)
        if not fix_prime_implacants:
            return True
        else:
            #print("VALID: ", prime_implicants)
            return False

    




    @staticmethod
    @analysis
    def fix_prime_implicants_bica(prime_implicants):
        valid_prime_implicants = list()
        for prime_implicant in prime_implicants:
            if TemporalFormula.is_valid_prime_implicant(prime_implicant):
                valid_prime_implicants.append(prime_implicant)

        return valid_prime_implicants

    
    @staticmethod
    def is_valid_prime_implicant(prime_implicant):
        for literal_i in prime_implicant:
            for literal_j in prime_implicant:
                if literal_i == literal_j:
                    continue
                are_failure = TemporalFormula.are_failure_literals(literal_i, literal_j)
                if are_failure:
                    return False
        return True

    @staticmethod
    def are_failure_literals(literal_i, literal_j):
        return TemporalFormula.subsumes(literal_i, "-" + literal_j)


    @staticmethod
    @analysis
    def subsumes(future1, future2, **kwargs):
        #future1 subsumes future2

        if future1 == future2:
            return True   

        future1List = TemporalFormula.getStrToList(future1, changeNegAlwaysEventually = True, extract_negs_from_nexts=False,  split_futures = False, strict_future_formulas = False, **kwargs)
        future1Literals = TemporalFormula.get_literals(future1List, **kwargs)

        future2List = TemporalFormula.getStrToList(future2, changeNegAlwaysEventually = True, extract_negs_from_nexts=False, split_futures = False, strict_future_formulas = False, **kwargs)
        future2Literals = TemporalFormula.get_literals(future2List, **kwargs)


        if TemporalFormula.is_next(future1List[0], **kwargs):
            future1List = TemporalFormula.include_next_to_formula(future1List, **kwargs)

        if TemporalFormula.is_next(future2List[0], **kwargs):
            future2List = TemporalFormula.include_next_to_formula(future2List, **kwargs)

        if future1Literals >= future2Literals:
                if TemporalFormula.is_in_interval_success(future1List, future2List, **kwargs):
                    literal1WithOutTemp = TemporalFormula.delete_temp_ops(future1List, **kwargs)
                    literal2WithOutTemp = TemporalFormula.delete_temp_ops(future2List, **kwargs)
                    f = ['&', literal1WithOutTemp, TemporalFormula.push_negs(['-', literal2WithOutTemp], **kwargs)]
                    is_sat_f = TemporalFormula.is_sat(f, **kwargs)
                    if not is_sat_f:
                        return True                    
        return False

    @staticmethod
    @analysis
    def is_sat(formula, **kwargs):

        """
        This procedure takes as input a Boolean formula and returns a list of sets,
        representing a DNF equivalent to the original formula, of minimal size.
        This is exactly a cover of the formula by prime implicants.

        It calls the tool Bica to do this.

        The input formula can be either an existential Boolean circuit, built by using
        the class Circuit, or a list of lists. For example,

            ['&', 'True', ['&', ['->', ['&', ['-', 'p'], ['&', ['X', 'p'], ['&', ['X', ['X', 'p'] ...

        The flags allow to display information and delete temporary files.

        - Created on Sat Jun 26 13:34:12 2021

        - Author: Noel Arteche


        """


        # Create a circuit object with the benchmark to be used.
        # (check first whether it is already a circuit, or whether you need
        # to convert it from a list format given as input).
        C = Circuit()
        formula = correct_bica_formula(formula)
        if isinstance(formula, Circuit):
            C = formula
        else:
            C.list_to_circ(formula)

        # Create a DIMACS file tuned for BICA with the positive formula.
        C.write_in_DIMACS("pos.cnf", add_BICA_line=True)



        return MiniSAT("pos.cnf") == "SAT"



    ################################



    ######### GET FUNCTIONS ########
    
    @staticmethod
    @analysis
    def get_neg_literal(literal, **kwargs):
        first_char = literal[0]
        if first_char in NEG_OPERATORS:
            return literal[1:]
        else:
            return "-" + literal
    
    @staticmethod
    @analysis
    def get_variable(literal, **kwargs):
        if literal[0] == "-":
            return literal[1:]
        else:
            return literal
    
    @staticmethod
    @analysis
    def get_temporal_op_limits(op, **kwargs):
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
    
    @staticmethod
    @analysis
    def get_temporal_limits(formula, **kwargs):
        if TemporalFormula.is_next(formula[0], **kwargs):
            cNext = TemporalFormula.get_next_n(formula[0], **kwargs)
            return cNext, cNext
        elif TemporalFormula.is_eventually(formula[0], **kwargs) or TemporalFormula.is_always(formula[0], **kwargs):
            return TemporalFormula.get_temporal_op_limits(formula[0], **kwargs)
        else:
            return 0, 0
    
    @staticmethod
    @analysis
    def get_number_nexts(formula, **kwargs):
        if TemporalFormula.is_next(formula[0], **kwargs):
            return 1 +  TemporalFormula.get_number_nexts(formula[1], **kwargs)
        else:
            return 0
    
    @staticmethod
    @analysis
    def getStrToList(formulaStr, changeNegAlwaysEventually = False, extract_negs_from_nexts = False, split_futures = False, strict_future_formulas = False, **kwargs):
        return TemporalFormula(formulaStr, changeNegAlwaysEventually = changeNegAlwaysEventually, extract_negs_from_nexts = extract_negs_from_nexts, split_futures=split_futures, strict_future_formulas=strict_future_formulas, **kwargs).ab
    

    @staticmethod
    @analysis
    def get_variable(formula, **kwargs):
        if TemporalFormula.is_temp_op(formula[0], **kwargs):
            if TemporalFormula.is_eventually(formula, **kwargs):
                deleteEventuality = formula.split("]", 1)
                return TemporalFormula.get_variable(deleteEventuality[1], **kwargs)
            else:
                return TemporalFormula.get_variable(formula[1:], **kwargs)
        elif formula[0] == "-":
            return formula[1:]
        else :
            return formula
    
    @staticmethod
    @analysis
    def get_literals(formula, **kwargs):
            if isinstance(formula, str):
                return {formula}
            elif len(formula) == 2:
                return TemporalFormula.get_literals(formula[1], **kwargs)
            else:
                res1 = TemporalFormula.get_literals(formula[1], **kwargs)
                res2 = TemporalFormula.get_literals(formula[2], **kwargs)
                return res1 | res2  

    @staticmethod
    @analysis
    def get_next_n(next_op, **kwargs):
        if next_op == "X":
            return 1
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

    @staticmethod
    @analysis
    def get_env_actual_variables(formula, **kwargs):
        if isinstance(formula, str):
            if TemporalFormula.is_var_env(formula):
                return {formula}
            else:
                return set()
        elif len(formula) == 2:
            if TemporalFormula.is_neg(formula[0]):
                return  TemporalFormula.get_env_actual_variables(formula[1])
            else:
                return set()
        else:
            left_Formula_Env = TemporalFormula.get_env_actual_variables(formula[1])
            right_Formula_Env = TemporalFormula.get_env_actual_variables(formula[2])
            env_actual_assignments = left_Formula_Env.union(right_Formula_Env)
            if len(formula) > 3:
                for f in formula[3:]:
                    env_actual_assignments =  env_actual_assignments.union(TemporalFormula.get_env_actual_variables(f))

            return env_actual_assignments

    @staticmethod
    @analysis
    def get_all_dnf_temporal_formulas(dnf, info = dict(), **kwargs):
        res = set()
        for model in dnf:
            for f in model:
                if TemporalFormula.is_temp_formula(f, **kwargs):
                    res.add(f)
        add_info(info, "DNF Temporal Formulas (n): ", len(res))
        return res

    @staticmethod
    @analysis
    def get_all_assignments(var_set, **kwargs):
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

    @staticmethod
    @analysis
    def getStrToAb(formulaStr, strToAb, **kwargs):
        # if formulaStr not in strToAb:
        #     AbFormula = TemporalFormula(formulaStr, extract_negs_from_nexts=True, split_futures=False).ab
        #     strToAb[formulaStr] = AbFormula
        # return strToAb[formulaStr]
        return TemporalFormula(formulaStr, changeNegAlwaysEventually=False, extract_negs_from_nexts=True,  split_futures = False, strict_future_formulas = False, **kwargs).ab

    
    ################################


    ######## NEG FUNCTIONS #########
    
    @staticmethod
    @analysis
    def neg_formula_ab(formula, changeNegAlwaysEventually = True, **kwargs):
        """"
            Return formula negation
        """
        if isinstance(formula, str) and TemporalFormula.is_true(formula, **kwargs):
            return FALSE_SYMBOL
        elif isinstance(formula, str) and TemporalFormula.is_false(formula, **kwargs):
            return TRUE_SYMBOL
        elif TemporalFormula.is_neg(formula[0], **kwargs):
            return formula[1]
        elif TemporalFormula.is_and(formula[0], **kwargs):
            leftFormulaNeg = TemporalFormula.neg_formula_ab(formula[1], changeNegAlwaysEventually, **kwargs)
            rightFormulaNeg = TemporalFormula.neg_formula_ab(formula[2], changeNegAlwaysEventually, **kwargs)
            neg_formula =  [OR_OPERATOR,leftFormulaNeg, rightFormulaNeg]
            if len(formula) > 3:
                for f in formula[3:]:
                    extra_formula = TemporalFormula.neg_formula_ab(f, changeNegAlwaysEventually, **kwargs)
                    neg_formula.append(extra_formula)
            return neg_formula
        elif TemporalFormula.is_or(formula[0], **kwargs):
            leftFormulaNeg = TemporalFormula.neg_formula_ab(formula[1], changeNegAlwaysEventually, **kwargs)
            rightFormulaNeg = TemporalFormula.neg_formula_ab(formula[2], changeNegAlwaysEventually, **kwargs)
            neg_formula = [AND_OPERATOR,leftFormulaNeg, rightFormulaNeg]
            if len(formula) > 3:
                for f in formula[3:]:
                    extra_formula = TemporalFormula.neg_formula_ab(f, changeNegAlwaysEventually, **kwargs)
                    neg_formula.append(extra_formula)
            return neg_formula
        elif TemporalFormula.is_next(formula[0], **kwargs):
            subformulaNeg = TemporalFormula.neg_formula_ab(formula[1], changeNegAlwaysEventually, **kwargs)
            return [formula[0], subformulaNeg]
        elif TemporalFormula.is_eventually(formula[0], **kwargs):
            subformulaNeg = TemporalFormula.neg_formula_ab(formula[1], changeNegAlwaysEventually, **kwargs)
            if changeNegAlwaysEventually:
                return [TemporalFormula.F_to_G(formula[0], **kwargs), subformulaNeg]
            else:
                return [NEG_OPERATOR, formula]

        elif TemporalFormula.is_always(formula[0], **kwargs):
            subformulaNeg = TemporalFormula.neg_formula_ab(formula[1], changeNegAlwaysEventually, **kwargs)
            if changeNegAlwaysEventually:
                return [TemporalFormula.G_to_F(formula[0], **kwargs), subformulaNeg]
            else:
                return [NEG_OPERATOR, formula]
        else:
            return [NEG_OPERATOR, formula]


    @staticmethod
    @analysis
    def neg_strict_futures_from_safety_formula(strict_future_formulas, **kwargs):

        if isinstance(strict_future_formulas, str):
            return TemporalFormula.neg_strict_future_literal(strict_future_formulas)
        neg_strict_future_formulas = list()
        for strict_future_formulas_i in strict_future_formulas:
            if isinstance(strict_future_formulas_i, list):
                neg_strict_future_formulas_i = list()
                for strict_future_formulas_i_j in strict_future_formulas_i:
                    neg_strict_future_formulas_i_j = TemporalFormula.neg_strict_future_literal(strict_future_formulas_i_j)
                    neg_strict_future_formulas_i.append(neg_strict_future_formulas_i_j)
                neg_strict_future_formulas.append(neg_strict_future_formulas_i)
            else:
                neg_strict_future_formulas_i = TemporalFormula.neg_strict_future_literal(strict_future_formulas_i)
                neg_strict_future_formulas.append(neg_strict_future_formulas_i)

        return neg_strict_future_formulas

    @staticmethod
    def neg_strict_future_literal(literal):
        if TemporalFormula.is_and(literal):
            return OR_OPERATOR
        elif  TemporalFormula.is_or(literal):
            return AND_OPERATOR
        else:
            if TemporalFormula.is_neg(literal[0]):
                return literal[1:]
            else:
                return "-" + literal



    
    
    @staticmethod
    @analysis          
    def extract_neg_from_nexts(formula, **kwargs):
        if isinstance(formula, str):
            return formula
        elif TemporalFormula.is_binary(formula, **kwargs):
            left_formula = TemporalFormula.extract_neg_from_nexts(formula[1], **kwargs)
            right_formula = TemporalFormula.extract_neg_from_nexts(formula[2], **kwargs)
            return [formula[0], left_formula, right_formula]
        elif TemporalFormula.is_next(formula[0], **kwargs):
            if len(formula[1]) == 2 and TemporalFormula.is_neg(formula[1][0], **kwargs):
                neg_left_formula = TemporalFormula.neg_formula_ab(formula[1], **kwargs)
                return [NEG_OPERATOR, [formula[0], neg_left_formula]]
            else:
                return formula
        else:
            return formula

    
    @staticmethod
    @analysis
    def neg_literal(strLiteral, **kwargs):
        """
            Return the negation of the given literal
        """
        if strLiteral[0] == "-":
            return strLiteral[1:]
        else:
            return "-" + strLiteral

    
    @staticmethod
    @analysis
    def simple_negation_ab(l, **kwargs):
        if l == "True":
            return "False"
        if l == "False":
            return "True"
        if l[0] == "-":
            return l[1:]
        else:
            return ['-', l]
    
    @staticmethod
    @analysis
    def simple_formula_ab(f, **kwargs):
        if f[0] == "-":
            return ['-', f[1:]]
        else:
            return f


    @staticmethod
    @analysis
    def are_equal_formulas(sf1, sf2, env_minimal_covering = list(), **kwargs):
        """
            True: if two separated formulas sf1 and sf2 are equivalent
        """

        if env_minimal_covering:
            neg_minimal_covering = TemporalFormula.neg_formula_ab(env_minimal_covering)
        else:
            env_minimal_covering = ['|', AUX_NODE, ["-", AUX_NODE]]
            neg_minimal_covering = ['&', AUX_NODE, ["-", AUX_NODE]]
        neg_sf1_ab = ['|', TemporalFormula.neg_separated_formulas_to_ab(sf1, **kwargs), neg_minimal_covering]

        neg_sf2_ab = ['|', TemporalFormula.neg_separated_formulas_to_ab(sf2, **kwargs), neg_minimal_covering]
        

        sf1_ab = ['&', TemporalFormula.separated_formulas_to_ab(sf1, **kwargs), env_minimal_covering]
        sf2_ab = ['&', TemporalFormula.separated_formulas_to_ab(sf2, **kwargs), env_minimal_covering]

        f1toAB = ['&', sf2_ab, neg_sf1_ab]
        f2toAB = ['&', sf1_ab, neg_sf2_ab]



        if TemporalFormula.is_sat(f1toAB, **kwargs):
            return False
        elif TemporalFormula.is_sat(f2toAB, **kwargs):
            return False
        else:
            return True


    @staticmethod
    @analysis
    def neg_separated_formulas_to_ab(separated_formulas, **kwargs):
        """
            Return the negation of the given separated formulas 
        """
        to_ab = ['&']
        for separated_formula in separated_formulas:
            separated_formula_ab = TemporalFormula.neg_separated_formula_to_ab(separated_formula, **kwargs)
            if separated_formula_ab:
                to_ab.append(separated_formula_ab)
        if len(to_ab) == 1:
            return list()
        elif len(to_ab) == 2:
            return to_ab[1]
        else:
            return to_ab

    @staticmethod
    @analysis
    def neg_separated_formula_to_ab(separated_formula, **kwargs):
        """
            Return the negation of the given separated formula 
        """
        literals_sys = separated_formula['Y']
        literals_env = separated_formula['X']
        futures = separated_formula['Futures']

        separated_formula_ab = ['|']
        
        for literal in literals_env:
            separated_formula_ab.append(TemporalFormula.simple_negation_ab(literal, **kwargs))
        
        # for literal in literals_sys:
        #     separated_formula_ab.append(simple_negation_ab(literal))

        futures_ab = ['&']
        
        for future in futures:
            futures_i_ab = ['|']
            for f in future:
                futures_i_ab.append(TemporalFormula.simple_negation_ab(f, **kwargs))
        
            futures_i_ab = TemporalFormula.fix_ab_list(futures_i_ab, **kwargs)
            if futures_i_ab:  
                futures_ab.append(futures_i_ab)
        
        futures_ab = TemporalFormula.fix_ab_list(futures_ab, **kwargs)
        
        if futures_ab:
            separated_formula_ab.append(futures_ab)
        
        separated_formula_ab = TemporalFormula.fix_ab_list(separated_formula_ab, **kwargs)


        
        return separated_formula_ab

    ################################


    ######## DELETE FUNCTIONS ######

    @staticmethod
    @analysis
    def delete_neg_str(formula, **kwargs):
        return formula.replace("-", "")

    @staticmethod
    @analysis
    def delete_temp_ops(formula, **kwargs):
        if TemporalFormula.is_temp_op(formula[0], **kwargs):
            return TemporalFormula.delete_temp_ops(formula[1], **kwargs)
        else:
            return formula

    ################################

    ######## SET FUNCTIONS #########

    @staticmethod
    @analysis
    def set_next_n(n, **kwargs):
        return "X[" + str(n) + "]"
    
    @staticmethod
    @analysis
    def set_always_interval(limitInf, limitSup, **kwargs):
        return ALWAYS_OPERATOR + "[" + str(limitInf) + "," + str(limitSup) + "]"
    
    @staticmethod
    @analysis
    def set_eventually_interval(limitInf, limitSup, **kwargs):
        return EVENTUALLY_OPERATOR + "[" + str(limitInf) + "," + str(limitSup) + "]"

    @staticmethod
    @analysis
    def empty_separated_formula(**kwargs):
        sf = dict()
        sf['X'] = set()
        sf['Y'] = set()
        sf['Futures'] = list()
        return sf

    @staticmethod
    @analysis
    def set_separated_formula(X, Y, F, **kwargs):
        sf = dict()
        sf['X'] = X
        sf['Y'] = Y
        sf['Futures'] = F
        return sf 

    ################################



    ######## PRINT FUNCTIONS #######
    
    @staticmethod
    @analysis
    def print_subsumptions(s, **kwargs):
        for key in s.keys():
            print(" ", key, " subsumes ", s[key])
    
    @staticmethod
    @analysis
    def print_separated_formula(formula, AND = " ∧ ", OR = " v ", **kwargs):
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


    ################################

    ##### CONVERSION FUNCTIONS #####

    
    @staticmethod
    @analysis    
    def G_to_F(op, **kwargs):
        return op.replace(ALWAYS_OPERATOR, EVENTUALLY_OPERATOR)
    
    @staticmethod
    @analysis
    def F_to_G(op, **kwargs):
        return op.replace(EVENTUALLY_OPERATOR, ALWAYS_OPERATOR)

    @staticmethod
    @analysis
    def to_str(formula, **kwargs):
        if isinstance(formula, str):
            return formula
        elif len(formula) == 2:
            if formula[0] == "-":
                return  formula[0] + TemporalFormula.to_str(formula[1], **kwargs)
            else:
                sub_str = TemporalFormula.to_str(formula[1], **kwargs)
                if sub_str.startswith('-') and 'X' in formula[0]:
                    return '-' + formula[0] + "(" + sub_str[1:] +")"
                else:
                    return formula[0] + "(" + sub_str +")"
        else:
            leftFormula = TemporalFormula.to_str(formula[1], **kwargs)
            rightFormula = TemporalFormula.to_str(formula[2], **kwargs)
            res = "(" + leftFormula + ")" + formula[0] + "(" + rightFormula + ")"
            if len(formula) > 3:
                for f in formula[3:]:
                    extra_formula =  TemporalFormula.to_str(f, **kwargs)
                    res = res + formula[0] + "(" + extra_formula + ")"

            return res
    @staticmethod
    @analysis
    def dnf_to_sf(dnf, subsumptions, env_vars = False, **kwargs):
        sf = TemporalFormula.calculate_separated_formulas(dnf, subsumptions, env_vars, **kwargs)
        return sf

    @staticmethod
    @analysis
    def model_to_separated_formula(model, subsumptions, sf_env_vars  = False, **kwargs):
        """
            Return a model in separated formula format
        """
        sf = TemporalFormula.empty_separated_formula(**kwargs)
        
        futures = set()
        for formula in list(model):
            if "X[" in formula or "F[" in formula or "G[" in formula:
                futures.add(formula)
                continue   
            else:
                if TemporalFormula.is_var_env(formula, **kwargs):
                    sf['X'].add(formula)
                else:
                    sf['Y'].add(formula)
        if not futures:
                futures = {"X[1]True"}
        sf['Futures'].append(futures)
        return sf

    @staticmethod
    @analysis
    def separated_formulas_to_ab(separated_formulas, **kwargs):
        to_ab = ['|']
        for separated_formula in separated_formulas:
            separated_formula_ab = TemporalFormula.separated_formula_to_ab(separated_formula, **kwargs)
            if separated_formula_ab:
                to_ab.append(separated_formula_ab)
        if len(to_ab) == 1:
            return list()
        elif len(to_ab) == 2:
            return to_ab[1]
        else:
            return to_ab    

    @staticmethod
    @analysis
    def separated_formula_to_ab(separated_formula, **kwargs):
        literals_sys = separated_formula['Y']
        literals_env = separated_formula['X']
        futures = separated_formula['Futures']

        separated_formula_ab = ['&']
        
        for literal in literals_env:
            separated_formula_ab.append(TemporalFormula.simple_formula_ab(literal, **kwargs))
        
        # for literal in literals_sys:
        #     separated_formula_ab.append(simple_formula_ab(literal))

        futures_ab = ['|']
        
        for future in futures:
            futures_i_ab = ['&']
            for f in future:
                futures_i_ab.append(TemporalFormula.simple_formula_ab(f, **kwargs))
        
            futures_i_ab = TemporalFormula.fix_ab_list(futures_i_ab, **kwargs)
            if futures_i_ab:  
                futures_ab.append(futures_i_ab)

        futures_ab = TemporalFormula.fix_ab_list(futures_ab, **kwargs)
        
        if futures_ab:
            separated_formula_ab.append(futures_ab)
        
        separated_formula_ab = TemporalFormula.fix_ab_list(separated_formula_ab, **kwargs)
        
        return separated_formula_ab

    @staticmethod
    @analysis
    def dnf_to_separated_formulas(models, subsumptions, **kwargs):    
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
                        if TemporalFormula.subsumes(fi, l, subsumptions, **kwargs):
                            break
                        elif TemporalFormula.subsumes(l, fi, subsumptions, **kwargs):
                            for fj in list(futures):
                                if TemporalFormula.subsumes(l, fj, subsumptions, **kwargs):
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

    @staticmethod
    def separated_formula_strict_futures_to_ab(strict_future_formulas):
        strict_future_next_formulas = [OR_OPERATOR]
        for or_strict_formula in strict_future_formulas:
            and_strict_next_formulas = [AND_OPERATOR]
            for and_strict_formula in or_strict_formula:
                and_strict_next_formulas.append(and_strict_formula)
            if len(and_strict_next_formulas) == 2:
                and_strict_next_formulas = and_strict_next_formulas[1]
            strict_future_next_formulas.append(and_strict_next_formulas)
        if len(strict_future_next_formulas) == 2:
            strict_future_next_formulas_next_rule_applied =  strict_future_next_formulas[1]

        elif len(strict_future_next_formulas) > 2:
            strict_future_next_formulas_next_rule_applied =  strict_future_next_formulas
        else:
            strict_future_next_formulas_next_rule_applied =  [OR_OPERATOR, AUX_NODE, ['-', AUX_NODE]]

        return strict_future_next_formulas_next_rule_applied

    

    ################################

    ##### CALCULATE FUNCTIONS ######

    @staticmethod
    @analysis
    def calculate_separated_formulas(dnf, subsumptions, sf_env_vars = False, **kwargs):
        processing_models = []
        for model in dnf:
            to_sf = TemporalFormula.model_to_separated_formula(model, subsumptions, sf_env_vars, **kwargs)
            processing_models.append(to_sf)
        return processing_models


    @staticmethod
    @analysis
    def calculate_dnf(formula, info = dict(), **kwargs):
        start = time.time()
        if formula == 'True':
            return list()
        if len(formula) < 3 or isinstance(formula, str):
            formula = ['&', formula, formula]
        print(formula)
        dnf = prime_cover_via_BICA(formula)
        add_info(info, "DNF(s): ", time.time()-start)
        add_info(info, "DNF(n): ", len(dnf))


        return dnf


    ################################


    ##### OTHER FUNCTIONS ##########

    @staticmethod
    @analysis
    def include_next_to_formula(formula, **kwargs):
        nexts = TemporalFormula.get_next_n(formula[0], **kwargs)
        if len(formula[1]) == 2:
            if TemporalFormula.is_always(formula[1][0], **kwargs):
                limitInf, limitSup = TemporalFormula.get_temporal_op_limits(formula[1][0], **kwargs)
                newLimitInf = str(limitInf + nexts)
                newLimitSup = str(limitSup + nexts)

                return [ALWAYS_OPERATOR + "[" +newLimitInf+","+newLimitSup+ "]", formula[1][1]]
        
            elif TemporalFormula.is_eventually(formula[1][0]):
                limitInf, limitSup = TemporalFormula.get_temporal_op_limits(formula[1][0], **kwargs)
                newLimitInf = str(limitInf + nexts)
                newLimitSup = str(limitSup + nexts)

                return [EVENTUALLY_OPERATOR + "[" +newLimitInf+","+newLimitSup+ "]", formula[1][1]]

            elif TemporalFormula.is_next(formula[1][0], **kwargs):
                n = TemporalFormula.get_next_n(formula[1][0], **kwargs)
                return "X[" + str(n+nexts) + "]" + formula[1][1]
            else:
                return formula 


        else:
            return formula

    @staticmethod
    @analysis
    def fix_ab_list(ab, **kwargs):
        if not ab:
            return list()
        if ab[0] in AND_OPERATORS + OR_OPERATORS:
            if len(ab) <= 1:
                return list()
            if len(ab) == 2:
                return ab[1]
            else:
                return ab

    @staticmethod
    @analysis
    def add_to_closure(strFormula, strToAb, **kwargs):
        if strFormula not in strToAb:
            AbFormula = TemporalFormula(strFormula).ab
            strToAb[strFormula] = AbFormula

    @staticmethod
    @analysis
    def split_future_formula(formula_ab, **kwargs):
        if TemporalFormula.is_next(formula_ab[0], **kwargs):
            assert TemporalFormula.is_next(formula_ab[0], **kwargs)
            n_nexts = TemporalFormula.get_next_n(formula_ab[0], **kwargs)
            op_next_minus_1 = NEXT_OPERATOR + "[" + str(n_nexts-1) + "]"
            if n_nexts-1 == 0:
                return ['X[1]', formula_ab[1]]
            else:
                return ['X[1]', [op_next_minus_1, formula_ab[1]]]
        else:
            assert TemporalFormula.is_always(formula_ab[0], **kwargs) or TemporalFormula.is_eventually(formula_ab[0], **kwargs)
            limitInf, limitSup = TemporalFormula.get_temporal_op_limits(formula_ab[0], **kwargs)
            if limitInf == limitSup:
                return TemporalFormula.generate_next(formula_ab[1], limitInf, **kwargs)
            new_limit_sup = limitSup-1
            left_children = TemporalFormula.generate_next(formula_ab[1], limitInf, **kwargs)
            if limitInf == new_limit_sup:
                right_children = TemporalFormula.generate_next(formula_ab[1], limitInf+1, **kwargs)
            else:
                limitsSupMinus1 = formula_ab[0][0] + "[" + str(limitInf) +  "," + str(new_limit_sup) + "]"
                right_children = ['X[1]', [limitsSupMinus1, formula_ab[1]]]

            if TemporalFormula.is_always(formula_ab[0], **kwargs):
                return [AND_OPERATOR, left_children, right_children]
            else:
                return [OR_OPERATOR, left_children, right_children]

        

    ################################