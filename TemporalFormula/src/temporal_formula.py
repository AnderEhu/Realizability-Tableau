import copy
import itertools
from posixpath import split
import sys
import time
from numpy import fix
from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor

from Solver.bica import prime_cover_via_BICA
from Solver.circuit import Circuit
from tools import MiniSAT, add_info, analysis, correct_bica_formula


######################### Constants #########################

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

###########################################################






class TemporalFormula(NodeVisitor):

    """
        Our Temporal Formulas are constructed using the classical operators of the propositional logic together
        with the following temporal operators:
            - Next, represented with "X" or "X[n]"
            - Bounded Always, represented with "G[n, m]"
            - Bounded Eventually, represented with "F[n, m]"

        Some examples of previous temporal operators:
            - Next: XXa, X[2]a, X[100]a, Xa, XXXXXXXXXXXXXa
            - Bounded Always: G[0,1]a, G[100,200]a, G[5, 10]a
            - Bounded Eventually: F[0,1]a, F[100,200]a, F[5, 10]a

        TemporalFormula class aim to transform an input string representing the temporal formula into a equivalente list of list. Moreover, 
        there are implemented several functions that allows us to modify temporal formulas.

        TemporalFormula arguments are:
            - changeNegAlwaysEventually: if its true, 
                1.For bounded always negation it change to equivalent bounded eventually: -G[n,m]phi == F[n,m]-phi
                2.For bounded eventually negation it change to equivalent bounded eventually: -F[n,m]phi == G[n,m]-phi
            - extract_negs_from_nexts: if its true, negation operator is extracted from next formulas.
            - split_futures: if its true, bounded always/eventualities are splited as follows:
                1. For bounded always: G[n, m] phi == phi & XG[n, m-1]phi
                2. For bounded eventually: F[n, m] phi == phi | XF[n, m-1]phi
            - strict_future_formulas:  if its true, temporal formulas can only represent strict future, that is:
                1. For bounded always: G[0, m] phi == phi & XG[0, m-1]phi
                2. For bounded eventually: F[0, m] phi == phi | XF[0, m-1]phi
        

    """
    def __init__ (self, formulas, 
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
        self.formulas = formulas
        self.ab = self.calculate_ab(self.formulas, **kwargs)
    

    
    @analysis    
    def calculate_ab(self, formulas_str, **kwargs):
        """
            calculate_ab transform an input string of a conjunction temporal formulas in an arbitrary form into a list of lists that represent the equivalent NNF temporal formula.
            Args:
                formulas_str:  string of a temporal formula in an arbitrary form
            Returns:
                Equivalent NNF formula as a list of lists
                
        """
        formulas_ab = self.__calculate_ab(formulas_str, **kwargs)
        return formulas_ab
    
    def __calculate_ab(self, formulas_str, **kwargs):
        """
            __calculate_ab transform an input string of a conjunction temporal formulas in an arbitrary form into a list of lists that represent the equivalent NNF temporal formula.
            Args:
                formulas_str:  string of a temporal formula in an arbitrary form
            Returns:
                Equivalent NNF formula as a list of lists
                
        """
        if isinstance(formulas_str, str):
            formulas_str.replace("\t","").replace(" ", "").replace("\n","") #Eliminate spaces, linebreaks and tab
            ast = self.__parse_formula(formulas_str, **kwargs) #Equivalent abstract sintax tree
            ast_to_ab = self.visit(ast) #Transform ast formula into a list of lists representation
            ab_next_pushed =  TemporalFormula.push_nexts(ast_to_ab, **kwargs) # Push next in front of the atoms
            formulas_ab = TemporalFormula.push_negs(ab_next_pushed, self.changeNegAlwaysEventually, **kwargs) # Push negations in front of the atoms
            if self.extract_negs_from_nexts:
                formulas_ab = TemporalFormula.extract_neg_from_nexts(formulas_ab, **kwargs) #Extract negation operator from next formulas
            return formulas_ab
        elif len(formulas_str) == 1:
            return self.__calculate_ab(formulas_str[0], **kwargs)
        else:

            formulas_ab = ['&']
            formulas_ab += [self.__calculate_ab(formula_str, **kwargs) for formula_str in formulas_str]
            
            return formulas_ab

    def generic_visit(self, node, children):    
        """
        generic_visit is a functions used by Parsimonious visit function for traverse an abstract sintax tree. In our case, generic_visit
        transform abs formula into a list o lists formula.
        
        more info: https://github.com/erikrose/parsimonious/blob/master/parsimonious/nodes.py

        """
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
        elif len(children) == 3 and children[1] in IMPLICATION_OPERATORS: # (a -> b) == (-a | b) == ["|", ["-", "a"], ["b"]]
            return [OR_OPERATOR, [NEG_OPERATOR, children[0]], children[2]]
        elif len(children) == 3 and children[1] in DOUBLE_IMPLICATION_OPERATORS: # (a <--> b) == ((-a | b) & (-b | a)) == [["|", ["-", "a"], ["b"]], ["|", ["-", "b"], ["a"]]]]
            return [AND_OPERATOR, [OR_OPERATOR,[NEG_OPERATOR, children[0]],children[2]], [OR_OPERATOR,[NEG_OPERATOR, children[2]],children[0]]]
        else:
            assert children[0] == OPEN_PARENTHESIS_SYMBOL
            return children[1]

    def __general_visit_atom(self, node):
        if node.text in TRUE_SYMBOLS:
            return [OR_OPERATOR, AUX_NODE, NEG_AUX_NODE] # True is represented as a tautology aux_var | -aux_var, this is done for the correct functioning of BICA
        elif node.text in FALSE_SYMBOLS:
            return [AND_OPERATOR, AUX_NODE, NEG_AUX_NODE] # False is represented as a contradiction aux_var & -aux_var, this is done for the correct functioning of BICA
        else:
            return node.text

    def __general_visit_eventually(self, children):
        return self.__general_visit_always_or_eventually(children, EVENTUALLY_OPERATOR)

    def __general_visit_always(self, children):
        return self.__general_visit_always_or_eventually(children, ALWAYS_OPERATOR)

    def __split_future_at_general_visit(self, children, op):

        limitInf, limitSup = TemporalFormula.get_eventually_always_op_limits(children[0])
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


    def __general_visit_always_or_eventually(self, children, op):
        
        if self.split_futures or self.strict_future_formulas:
            return self.__split_future_at_general_visit(children, op)
        else:
            return [children[0], children[1]]

    @analysis
    def __parse_formula(self, str, **kwargs):
            grammar = Grammar(
                """
                Bicondicional = (Condicional "<-->" Bicondicional) / Condicional
                Condicional = (Disyuncion "->" Condicional) / Disyuncion
                Disyuncion =  (Conjuncion ("||" / "|")  Disyuncion) / Conjuncion
                Conjuncion = (Literal ("&&" / "&") Conjuncion) / Literal
                Literal =  (Atomo) / ((Neg / Eventually / Next / Globally ) Literal)
                Atomo = True / False /  Var / Agrupacion
                Agrupacion = "(" Bicondicional ")"
                Var = ~r"[a-zA-EH-WY-Z0-9][a-zA-Z0-9_]*"
                Next = ~r"X[[0-9]+]" / "X"
                Eventually = ~r"F[[0-9]+,[0-9]+]" 
                Globally = ~r"G[[0-9]+,[0-9]+]"
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
            Given a formula in a list of lists representation and accumulation number of next (c), generate pushed next
            Args:
                formula:  list of lists formula
                c: number of previous nexts
            Returns:
                Equivalent list of lists formula with conjunction of previuous next and formula next pushed in front of literals.
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
            c += TemporalFormula.get_next_n(formula[0], **kwargs)
            subformulaNext = TemporalFormula.next(formula[1], c, **kwargs)
            return subformulaNext
        elif  TemporalFormula.is_neg(formula[0], **kwargs):
            return [NEG_OPERATOR, TemporalFormula.next(formula[1], c, **kwargs)]
        else:
            return TemporalFormula.generate_next(formula, c, **kwargs)

    @staticmethod
    @analysis
    def generate_next(formula, n, extract_negs_from_nexts = False, **kwargs):

        """
            Given a formula and a integer n, generate_next returns a next formula equivatent to n nexts of 'formula'

            Args:
                formula: list of lists temporal formula
                n: number of nexts
                extract_negs_from_nexts: if its true, negation operator is extracted from next formulas.

            Returns:
                list of lists equivalent a next formula with n nexts of 'formula'

        """
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
        Push negs in front of atoms 

        Args:
            - formula: list of lists equivatent to a temporal formula
            - changeNegAlwaysEventually: if its true, 
                1.For bounded always negation it change to equivalent bounded eventually: -G[n,m]phi == F[n,m]-phi
                2.For bounded eventually negation it change to equivalent bounded eventually: -F[n,m]phi == G[n,m]-phi

        Returns:
            list of lists of formula with the negation in front of atoms

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
        Push nexts in front of atoms 

        Args:
            - formula: list of lists equivatent to a temporal formula

        Returns:
            list of lists of formula with the nexts in front of atoms

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
            c = TemporalFormula.get_next_n(formula[0], **kwargs)
            rightFormulaNext = TemporalFormula.next(formula[1], c, **kwargs)

            return rightFormulaNext
            
        else:
            return formula

    ###### BOOLEAN  FUNCTIONS ######
    @staticmethod
    @analysis
    def is_neg(op, **kwargs):
        """
        Given an operator op return True if op is negation operator, otherwise, False
        """
        return isinstance(op, str) and op in NEG_OPERATORS

    @staticmethod
    @analysis
    def is_and(op, **kwargs):
        """
        Given an operator op return True if op is and operator, otherwise, False
        """
        return isinstance(op, str) and op in AND_OPERATORS

    @staticmethod
    @analysis
    def is_or(op, **kwargs):
        """
        Given an operator op return True if op is or operator, otherwise, False
        """
        return isinstance(op, str) and op in OR_OPERATORS

    @staticmethod
    @analysis
    def is_next(op, **kwargs):
        """
        Given an operator op return True if op is next operator, otherwise, False
        """
        return isinstance(op, str) and ((op in NEXT_OPERATOR) or (len(op) > 3 and op[0] in NEXT_OPERATORS and op[1] == "["))

    @staticmethod
    @analysis
    def is_next_formula(formula, **kwargs):
        """
        Given a temporal formula as a list of list, return True if the first element of the list is a next operator, otherwise false.
        For example:
            - ['X[3]', 'a'], return True
            - ['F[1,2]', 'a'] return False

        """
        return TemporalFormula.is_next(formula[0])
    
    @staticmethod
    @analysis
    def is_eventually(op, **kwargs):
        """
        Given a temporal formula as a list of list, return True if the first element of the list is a eventually operator, otherwise false.
        For example:
            - ['F[1,2]', 'a'] return True
            - ['X[3]', 'a'], return False


        """
        return isinstance(op, str) and  len(op) > 5 and op[0] in EVENTUALLY_OPERATORS and op[1] == "["
    
    @staticmethod
    @analysis
    def is_always(op, **kwargs):
        """
        Given a temporal formula as a list of list, return True if the first element of the list is a always operator, otherwise false.
        For example:
            - ['G[2,5]', 'a'], return True
            - ['F[1,2]', 'a'] return False

        """
        return isinstance(op, str) and  len(op) > 5 and op[0] in ALWAYS_OPERATORS and op[1] == "["
    
    @staticmethod
    @analysis
    def is_var_env(var, **kwargs):
        """
        Given a variable as a string, return True if var is an environment variable, otherwise, False
        """
        return len(var) > 2 and var[-2:] == "_e" 
    
    @staticmethod
    @analysis
    def is_true(formula, **kwargs):
        """
        Given formula return if formula is a True statement symbol, otherwise, False
        """
        return isinstance(formula, str) and formula in TRUE_SYMBOLS
    
    @staticmethod
    @analysis
    def is_false(formula, **kwargs):
        """
        Given formula return if formula is a False statement symbol, otherwise, False
        """
        return isinstance(formula, str) and formula in FALSE_SYMBOLS
    
    @staticmethod
    @analysis
    def is_unary(formula, **kwargs):
        """
        Given a temporal formula as a list of list, return True if the first element of the list is a unary operator, otherwise false. 
        Moreover, unary operator are ones that have two elements, first element represent a temporal operator (Next, Eventually or Always)  and second element 
        a temporal formula.
        For example:
            - ['X[3]', 'a'], return True
            - ['F[1,2]', 'a'] return True
            - 'a' return False
            - ['&', ['X[3]', 'a'], 'a']
        """
        return isinstance(formula, list) and len(formula) == 2
    
    @staticmethod
    @analysis
    def is_binary(formula, **kwargs):
        """
        Given a temporal formula as a list of list, return True if the first element of the list is a binary operator, otherwise false. 
        Moreover, a binary operator are ones that have three elements, first element represent a boolean operator (And or Or) and second/third element 
        a temporal formula.
        For example:
            - ['&', ['X[3]', 'a'], 'a'], return True
            - ['&', ['X[3]', 'a'], 'a'] return True
            - ['&', ['F[1,2]', 'a'], 'a'] return True
            - 'a' return False
            - ['X[3]', 'a'], return True return False
            - ['F[1,2]', 'a'] return True return False
        """
        return isinstance(formula, list) and len(formula) >= 3
    

    
    @staticmethod
    @analysis
    def is_temp_op(op, **kwargs):
        """
        Given a operator op as a string, return True if op is a temporal operator, otherwise, False
        """
        return isinstance(op, str) and (TemporalFormula.is_next(op, **kwargs) or TemporalFormula.is_always(op, **kwargs) or TemporalFormula.is_eventually(op, **kwargs))
    

    @staticmethod
    @analysis 
    def is_in_interval_success(phiAb, alphaAb, **kwargs):
        """
            Returns if phiAB temporal operator interval can subsume alphaAb temporal operator interval, ej G[0,4] subsumes G[0,1]
            Args:
                -phiAb: temporal formula as a list of lists
                -alphaAb: temporal formula as a list of lists

            Returns:
                True, if phiAB temporal operator interval can subsume alphaAb temoral operator interval, otherwise, False

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
    def fix_prime_implicants_bica(prime_implicants):
        """
            Given a list of prime implicants, return the prime implicants that are consistent. Inconsistencies can appear due to the booleanization
            of temporal formulas, for example, (G[1,5]a & G[1,5]-a) return the prime implicant {G[1,5]a, G[1,5]-a} but G[1,5]a and G[1,5]-a are inconsistent. Applying
            this function previous prime implicant would be deleted.

            Args:
                prime_implicants: list of prime implicants

            Returns:
                list of consistent prime implicants 
                

        """
        valid_prime_implicants = list()
        for prime_implicant in prime_implicants:
            if TemporalFormula.is_valid_prime_implicant(prime_implicant):
                valid_prime_implicants.append(prime_implicant)

        return valid_prime_implicants

    
    @staticmethod
    def is_valid_prime_implicant(prime_implicant):
        """
            Given a prime implicants, return  if it is consistent. Inconsistencies can appear due to the booleanization
            of temporal formulas, for example, (G[1,5]a & G[1,5]-a) return the prime implicant {G[1,5]a, G[1,5]-a} but G[1,5]a and G[1,5]-a are inconsistent. Applying
            this function previous prime implicant return False.

            Args:
                prime_implicants: list of prime implicants

            Returns:
                if return True, prime implicant is consistent, otherwise, it found a inconsistency
                

        """

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
        #Cambiar aplicarcar reglar de inconsistencias
        return TemporalFormula.subsumes(literal_i, "-" + literal_j)


    @staticmethod
    @analysis
    def subsumes(future1, future2, **kwargs):
        """
            Given two temporal formulas, future1 and future2, returns if future1 subsumes future2

            Args:
                future1: temporal formula as string
                future2: temporal formula as string

            Returns:
                returns True if future1 subsumes future2, otherwise, False
                

        """

        if future1 == future2: # Two equal formulas are always subsumed
            return True   

        future1List = TemporalFormula.getStrToList(future1, changeNegAlwaysEventually = True, extract_negs_from_nexts=False,  split_futures = False, strict_future_formulas = False, **kwargs)
        future2List = TemporalFormula.getStrToList(future2, changeNegAlwaysEventually = True, extract_negs_from_nexts=False, split_futures = False, strict_future_formulas = False, **kwargs)

        if TemporalFormula.is_next(future1List[0], **kwargs):
            future1List = TemporalFormula.include_next_to_formula(future1List, **kwargs)

        if TemporalFormula.is_next(future2List[0], **kwargs):
            future2List = TemporalFormula.include_next_to_formula(future2List, **kwargs)
            
        # Once temporal formula future1 and future2 are in the interval with the possibility of future1 subsumes future2
        # the formula that follows the temporal operator of future1 should subsume the formula that follows the temporal operator of future2, for example,
        # given G[0, 5]a and G[0,3](a|b), G[0, 5]a subsumes G[0,3](a|b)?, first we need to check the intervals of both temporal operator if G[0, 5] can 
        # sumbsume a formula in G[0,3], if yes, 'a' must subsume '(a|b)' so that G[0, 5]a subsumes G[0,3](a|b). Moreover, we will check the subsumption of a to b as follow,
        # (a|b) must be a logical consequence of (a), is it?, a -> (a | b), so -(a ->(a|b)) must be unsat, consequently, we will ask to the sat solver if (a & -a & b) is unsat,
        # as if it is,  G[0, 5]a subsumes G[0, 5](a|b).

        if TemporalFormula.is_in_interval_success(future1List, future2List, **kwargs):
            if TemporalFormula.is_temp_op(future1List[0]):
                literal1WithOutTemp = future1List[1]
            else:
                literal1WithOutTemp = future1List
            if TemporalFormula.is_temp_op(future2List[0]):
                literal2WithOutTemp = future2List[1]
            else:
                literal2WithOutTemp = future2List

            if literal1WithOutTemp == literal2WithOutTemp:
                return True
            else:
                f = ['&', literal1WithOutTemp, TemporalFormula.push_negs(['-', literal2WithOutTemp], **kwargs)] # -(N1 -> N2) == N1&-N2
                is_sat_f = TemporalFormula.is_sat(f, **kwargs)
                if not is_sat_f:
                    #print(future1, "subsumes", future2)
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



    @staticmethod
    def is_valid_assignment(assignment, valid_assignments):
        """
        Given an assigment of variables and a list of valid assignments, return True if assignment is consistent with valid_assignments, otherwise, False
        """
        for valid_assignment in valid_assignments:
            valid = True
            neg_literals_valid_assignment = [ TemporalFormula.neg_literal(env_literal) for env_literal in assignment]
            for neg_literal_valid_assignment in neg_literals_valid_assignment:
                if neg_literal_valid_assignment in valid_assignment:
                    valid = False
                    break
            if not valid:
                continue
            else:
                return True
        return False

    ################################



    ######### GET FUNCTIONS ########
    
    @staticmethod
    @analysis
    def get_neg_literal(literal, **kwargs):
        """
        Given a literal as a string, return the negation of it.
        For example:
            -'a' return '-a'
            -'-a' return 'a'
        """
        first_char = literal[0]
        if first_char in NEG_OPERATORS:
            return literal[1:]
        else:
            return "-" + literal

    
    @staticmethod
    @analysis
    def get_eventually_always_op_limits(op, **kwargs):
        """
        Given an always operator or eventually operator as string, return the limits of the given operator, for example:
        - G[1,2] return (1,2)
        - F[1,22] return (1,22)
        """
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
        """
        Given a temporal formula (Next, Always or Eventually) return a duple representing the temporal limits of the formula.
        For example:
            - G[1,2]a return (1,2)
            - F[50,200]a return (5,200)
            - X[10]a return (10,10)
            - a return (0,0)

        """
        if TemporalFormula.is_next(formula[0], **kwargs):
            cNext = TemporalFormula.get_next_n(formula[0], **kwargs)
            return cNext, cNext
        elif TemporalFormula.is_eventually(formula[0], **kwargs) or TemporalFormula.is_always(formula[0], **kwargs):
            return TemporalFormula.get_eventually_always_op_limits(formula[0], **kwargs)
        else:
            return 0, 0
    
    @staticmethod
    @analysis
    def getStrToList(formula_str, changeNegAlwaysEventually = False, extract_negs_from_nexts = False, split_futures = False, strict_future_formulas = False, **kwargs):
        """
        Given a temporal formula as string return a list of lists representation of it.
        """
        return TemporalFormula(formula_str, changeNegAlwaysEventually = changeNegAlwaysEventually, extract_negs_from_nexts = extract_negs_from_nexts, split_futures=split_futures, strict_future_formulas=strict_future_formulas, **kwargs).ab
    

    
    @staticmethod
    @analysis
    
    def get_literals(formula_ab, **kwargs):
        """
        Given a temporal formula, formula_ab, returns the set of literals included in formula_ab,
        for example, ['G[1,0]', 'a'] returns {a}

            Args:
                formula_ab: temporal formula as a list of lists

            Returns:
                returns the set of literals that includes formula_ab
            

        """
        if isinstance(formula_ab, str):
            return {formula_ab}
        elif len(formula_ab) == 2:
            return TemporalFormula.get_literals(formula_ab[1], **kwargs)
        else:
            res1 = TemporalFormula.get_literals(formula_ab[1], **kwargs)
            res2 = TemporalFormula.get_literals(formula_ab[2], **kwargs)
            return res1 | res2  

    @staticmethod
    @analysis
    def get_next_n(next_op, **kwargs):
        """
        Given a next opertor X[n], it returns number of next, that is, n

            Args:
                next_op: next operator (string)

            Returns:
                returns an integer representing the number of next of next operator
            

        """
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
        """
        Given a temporal formula as a list of lists, it returns the set of environment variables that take part in the present 

        Args: 
            -formula: temporal formula represented as a list of lists

        Returns:
            set of all environment variables (present)
        
        """
        if isinstance(formula, str):
            if TemporalFormula.is_var_env(formula):
                return {formula}
            else:
                return set()
        elif len(formula) == 2:
            if TemporalFormula.is_neg(formula[0]):
                return  TemporalFormula.get_env_actual_variables(formula[1])
            elif TemporalFormula.is_next(formula[0]):
                n = TemporalFormula.get_next_n(formula[0])
                if n == 0:
                    return  TemporalFormula.get_env_actual_variables(formula[1])
                else:
                    return set()
            else:
                limit_inf, _ = TemporalFormula.get_eventually_always_op_limits(formula[0])
                if limit_inf == 0:
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
    def get_str_to_ab_in_bica(formulaStr, strToAb, **kwargs): # TODO: Unificar con getStrToList

        is_neg = True if TemporalFormula.is_neg(formulaStr[0]) else False
        formulaStr_split = formulaStr[1:].split("]") if is_neg else formulaStr.split("]")
        formulaStr_split = [elem + "]" if i < len(formulaStr_split)-1 else elem for i, elem in enumerate(formulaStr_split)]
        formula_ab = list()
        if len(formulaStr_split) == 1:
            if formulaStr_split[0] in strToAb:
                formula_ab = strToAb[formulaStr_split[0]]
            else:
                formula_ab = TemporalFormula.get_simple_str_to_ab(formulaStr_split[0], strToAb)
        elif len(formulaStr_split) == 2:
            if formulaStr_split[1] in strToAb:
                last_formula_ab = strToAb[formulaStr_split[1]]
            else:
                last_formula_ab = TemporalFormula.get_simple_str_to_ab(formulaStr_split[1], strToAb)
            formula_ab = [formulaStr_split[0], last_formula_ab]

        elif len(formulaStr_split) == 3:
            if formulaStr_split[2][:-1] in strToAb:
                last_formula_ab = strToAb[formulaStr_split[2][:-1]]
            else:
                last_formula_ab = TemporalFormula.get_simple_str_to_ab(formulaStr_split[2][:-1], strToAb)
            formula_ab = [formulaStr_split[0], [formulaStr_split[1][1:], last_formula_ab]]

        else:
            assert False
        
        if is_neg:
            return ['-', formula_ab]
        else:
            return formula_ab

    @staticmethod
    def get_simple_str_to_ab(formula_str, strToAb):
        if formula_str in strToAb:
            formula_ab = strToAb[formula_str]
        else:
            formula_ab =  TemporalFormula(formula_str, changeNegAlwaysEventually=True, extract_negs_from_nexts=True,  split_futures = False, strict_future_formulas = False).ab
            strToAb[formula_str] = formula_ab
        return formula_ab


        

    @staticmethod
    def get_valid_env_valuations(all_assignments, valid_assignments):
        """
        Given a list of sets representing all valuation of literals and a list of sets representing valid ones, 
        return all_assignments compatibles with valid_assignments.
        For example:
         - all_assignments = [{'p_e'}, {'-p_e'}] and  valid_assignments = [{'p_e'}] return [{'p_e'}]
          - all_assignments = [{'p_e'}, {'-p_e'}] and  valid_assignments = [{'p_e', r_e}] return [{'p_e'}]
        """
        if not valid_assignments:
            return all_assignments
        all_valid_assignments = list()
        for assignment in all_assignments:
            if TemporalFormula.is_valid_assignment(assignment, valid_assignments):
                all_valid_assignments.append(assignment)
        return all_valid_assignments

    

        
        
    
    ################################


    ######## NEG FUNCTIONS #########
    
    @staticmethod
    @analysis
    def neg_formula_ab(formula, changeNegAlwaysEventually = True, **kwargs):
        """
        Negates a given formula formula

        Args:
            - formula: list of lists representing a temporal formula
            - changeNegAlwaysEventually: if its true, 
                1.For bounded always negation it change to equivalent bounded eventually: -G[n,m]phi == F[n,m]-phi
                2.For bounded eventually negation it change to equivalent bounded eventually: -F[n,m]phi == G[n,m]-phi

        Returns:
            'formula' negated

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
    def neg_future_sets_subsumption_ab(f):
        

        if isinstance(f, str):
            return TemporalFormula.simple_negation_ab(f)
        else:
            if f[0] == '-':
                return f[1]
            else:
                f_i_neg = list()
                for f_i in f:
                    f_i_neg.append(TemporalFormula.neg_future_sets_subsumption_ab(f_i))
                return f_i_neg

    
    
    @staticmethod
    @analysis          
    def extract_neg_from_nexts(formula, **kwargs):
        """
        Given a formula as a list of lists in a nnf form, if next operator are in front of negation operator, it change to be negation
        operator in fornt of next operator:

            Args:
                formula: nnf temporal formula as a list of lists

            Returns:
                nnf temporal formula but with the negations extracted from next formulas

            Example:
                Given ['X', ['-', 'a']] it changes to ['-', ['X', 'a']

        """
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
        Given a literal as string, return the negation, for example, a returns -a and -a return a

        Args:
            strliteral: literal as string

        Returns:
            returns negation of strLiteral as string


        """
        if strLiteral[0] == "-":
            return strLiteral[1:]
        else:
            return "-" + strLiteral

    
    @staticmethod
    @analysis
    def simple_negation_ab(formula_ab, **kwargs):
        """
        Given a temporal formula as list of lists, return the simple negation, for example, ['|', 'a', 'b'] returns ['-', ['|', 'a', 'b']]

        Args:
            formula_ab: temporal formula as list of lists

        Returns:
            returns negation of strLiteral as string


        """
        if formula_ab == "True":
            return [AND_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        elif formula_ab == "False":
            return [OR_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        elif formula_ab == "X[1]True":
            return "X[1]False"
        elif formula_ab == "X[1]False":
            return "X[1]True"
        elif formula_ab[0] == "-":
            return formula_ab[1:]
        elif formula_ab[0] == AND_OPERATOR:
            return OR_OPERATOR
        elif formula_ab[0] == OR_OPERATOR:
            return AND_OPERATOR
        else:
            return ['-', formula_ab]
    
    @staticmethod
    @analysis
    def simple_formula_ab(formula_str, **kwargs):
        """
        Given a temporal formula as string, if first element of the forma is a negation, returns a list, for example, '-a' return ['-', 'a']

        Args:
            formula_str: temporal formula as string

        Returns:
            returns a list if the first element of formula_str is the negation, otherwise, returns the same formula_str


        """
        if formula_str == "True":
            return [OR_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        if formula_str == "False":
            return [AND_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        if formula_str[0] == "-":
            return ['-', formula_str[1:]]
        else:
            return formula_str


    


    
    ################################


    ######## SET FUNCTIONS #########

    @staticmethod
    @analysis
    def set_next_n(n, **kwargs):
        """
        Given a integer n return an next^n operator. For example,
        - n = 5 return 'X[5]'
        """
        return "X[" + str(n) + "]"
    
    @staticmethod
    @analysis
    def set_always_interval(limitInf, limitSup, **kwargs):
        """
        Given two integers representing inferior and superior interval limits return an always operator, G[limitInf, limitSup]
        """
        return ALWAYS_OPERATOR + "[" + str(limitInf) + "," + str(limitSup) + "]"
    
    @staticmethod
    @analysis
    def set_eventually_interval(limitInf, limitSup, **kwargs):
        """
        Given two integers representing inferior and superior interval limits return an eventually operator, F[limitInf, limitSup]
        """
        return EVENTUALLY_OPERATOR + "[" + str(limitInf) + "," + str(limitSup) + "]"


    ################################



    ######## PRINT FUNCTIONS #######
    
    @staticmethod
    @analysis
    def print_subsumptions(s, **kwargs):
        for key in s.keys():
            print(" ", key, " subsumes ", s[key])

    @staticmethod
    def print_dnf(f):
        f_str = ""
        for fi in f:
            fi_str = "("
            for fij in fi:
                fi_str +=  fij + " \wedge "
            fi_str += ")"
            f_str += fi_str + "\\vee "
        print(f_str)
    
    


    ################################

    ##### CONVERSION FUNCTIONS #####

    
    @staticmethod
    @analysis    
    def G_to_F(op, **kwargs):
        """
        Given a always operator, G_to_F to an eventually operator. For example,
         - G[0,1] return F[0,1]
        """
        return op.replace(ALWAYS_OPERATOR, EVENTUALLY_OPERATOR)
    
    @staticmethod
    @analysis
    def F_to_G(op, **kwargs):
        """
        Given a eventually operator, F_to_G to an always operator. For example,
         - F[0,1] return G[0,1]
        """
        return op.replace(EVENTUALLY_OPERATOR, ALWAYS_OPERATOR)

    @staticmethod
    @analysis
    def to_str(formula, **kwargs):
        """
        Given a temporal formula as list of lists return the representation of it as string
        """
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
    def env_valuations_to_ab(env_valuations):
        """
        Given a list of sets representing a list of environment valuations return the representation as a temporal formula (list of lists). 
        Note that list represent Or and sets represents And, for example,
        - [{'p_e', 'r_e'}, {'-p_e', 'r_e'}] return ['|', ['&', 'p_e', 'r_e'], ['&', '-p_e', 'r_e']]
        """
        if not env_valuations:
            return [OR_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        env_covering_ab = ['|']
        for env_valuation in env_valuations:
            for literal in env_valuation:
                if TemporalFormula.is_neg(literal[0]):
                    env_covering_ab.append(['-', literal[1:]])
                else:
                    env_covering_ab.append(literal)
        fix_env_covering_ab = TemporalFormula.fix_ab_list(env_covering_ab)
        return fix_env_covering_ab  
    

    

    ################################

    ##### CALCULATE FUNCTIONS ######




    @staticmethod
    @analysis
    def calculate_dnf(formula, info = dict(), **kwargs):
        """
        Given a formula as a list of lists in an arbitrary form, return the equivalent DNF formula.
        """
        start = time.time()
        if formula == 'True':
            return list()
        if len(formula) < 3 or isinstance(formula, str):
            formula = ['&', formula, formula]
        dnf = prime_cover_via_BICA(formula)
        add_info(info, "DNF(s): ", time.time()-start)
        add_info(info, "DNF(n): ", len(dnf))


        return dnf


    ################################


    ##### OTHER FUNCTIONS ##########

    @staticmethod
    @analysis
    
    def include_next_to_formula(formula_ab, **kwargs):
        """
            Given a Next formula, if the following operator of next operator is a temporal operator, this function distribute next^i, for example,
            ['X[5]',['G[1,4]', 'a']] will return ['G[6,9]', 'a'] and ['X[1]', 'a'] will return ['X[1]', 'a']
            Args:
                formula_ab: list of lists temporal formula
            Returns:
                it distribute X[i] thought the formula if following operator is a temporal operator
        """
        nexts = TemporalFormula.get_next_n(formula_ab[0], **kwargs)
        if len(formula_ab[1]) == 2:
            if TemporalFormula.is_always(formula_ab[1][0], **kwargs):
                limitInf, limitSup = TemporalFormula.get_eventually_always_op_limits(formula_ab[1][0], **kwargs)
                newLimitInf = str(limitInf + nexts)
                newLimitSup = str(limitSup + nexts)

                return [ALWAYS_OPERATOR + "[" +newLimitInf+","+newLimitSup+ "]", formula_ab[1][1]]
        
            elif TemporalFormula.is_eventually(formula_ab[1][0]):
                limitInf, limitSup = TemporalFormula.get_eventually_always_op_limits(formula_ab[1][0], **kwargs)
                newLimitInf = str(limitInf + nexts)
                newLimitSup = str(limitSup + nexts)

                return [EVENTUALLY_OPERATOR + "[" +newLimitInf+","+newLimitSup+ "]", formula_ab[1][1]]

            elif TemporalFormula.is_next(formula_ab[1][0], **kwargs):
                n = TemporalFormula.get_next_n(formula_ab[1][0], **kwargs)
                return "X[" + str(n+nexts) + "]" + formula_ab[1][1]
            else:
                return formula_ab 


        else:
            return formula_ab

    @staticmethod
    @analysis
    def fix_ab_list(ab, **kwargs):
        fix_ab = list()
        if not ab:
            fix_ab = list()
        if ab[0] in AND_OPERATORS + OR_OPERATORS:
            if len(ab) == 1:
                return 'True'
            if len(ab) == 2:
                fix_ab = ab[1]
            else:
                fix_ab = ab

        return fix_ab

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
            limitInf, limitSup = TemporalFormula.get_eventually_always_op_limits(formula_ab[0], **kwargs)
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

    ###################################

 











    ##################333333333