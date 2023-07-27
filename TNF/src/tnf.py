
from TNF.src.subsumptions import Subsumptions


from TemporalFormula.src.temporal_formula import TemporalFormula
from TNF.src.separated_formula import SeparatedFormula
from tools import print_info_map, analysis

class TNF:
    """
        TNF formula is constructed from a temporal formula. 
        
        Args: 
            - temporal_formula: string o list of lists (see TemporalFormula class) representing a temporal formula in arbitrary form
            - env_constraints_str: in case of environment constraints, it must be included as a formula (string) for the calculation of minimal coverings.
        Optional Args:
            - info: dictionary that save importat information such as time execution
            - activated_apply_subsumptions: enable the subsumptions of formulas
            - activated_print_info: print important information 
            - activated_print_tnf: print the result of tnf 
            - activate_verification: verifies if dnf of temporal formula is equal to TNF
    """
    def __init__(self, temporal_formula, 
                    env_constraints_str = None,
                    env_constraints_ab = None,
                    info = dict(),
                    subsumptions = list(),
                    inconsistencies = dict(),
                    strToAb = dict(),
                    env_vars = None,
                    valid_env_valuations = None,
                    activated_apply_subsumptions = False, 
                    activated_print_info = False, 
                    activated_print_tnf = False,
                    activate_verification = False,
                    **kwargs):


        self.info = info
        self.inconsistencies = inconsistencies
        self.subsumptions = subsumptions
        self.strToAb = strToAb
        self.valid_env_valuations = valid_env_valuations
        self.activated_apply_subsumptions = activated_apply_subsumptions
        self.activated_print_info = activated_print_info 
        self.activated_print_tnf = activated_print_tnf
        self.activate_verification = activate_verification
        self.verification = False


        #First, if temporal formula is an string form, it calculate the equivalent list of list representation
        if isinstance(temporal_formula, str):
            self.formula = TemporalFormula(temporal_formula, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True).ab
        else:
            self.formula = temporal_formula
        
        
        #Then, environment minimal covering is calculated
        if env_vars:
            self.env_vars = env_vars
            self.all_env_valuations = TemporalFormula.get_all_assignments(self.env_vars,**kwargs)
        else:
            self.env_vars = TemporalFormula.get_environment_current_variables(self.formula)
            self.all_env_valuations = TemporalFormula.get_all_assignments(self.env_vars,**kwargs)

        if valid_env_valuations is None:

            if env_constraints_str:
                self.env_constraints = TemporalFormula(env_constraints_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs).ab
                self.valid_env_valuations = TemporalFormula.calculate_dnf(self.env_constraints, **kwargs)
                self.valid_env_valuations = TemporalFormula.get_valid_env_valuations(self.all_env_valuations, self.valid_env_valuations)
            elif env_constraints_ab:
                self.env_constraints = env_constraints_ab
                self.valid_env_valuations = TemporalFormula.calculate_dnf(self.env_constraints, **kwargs)
                self.valid_env_valuations = TemporalFormula.get_valid_env_valuations(self.all_env_valuations, self.valid_env_valuations)

            else:
                self.valid_env_valuations = self.all_env_valuations

        self.valid_env_valuations_ab = TemporalFormula.env_valuations_to_ab(self.valid_env_valuations)



        # Next, the equvialent DNF of formula is calculated
        self.dnf = TemporalFormula.calculate_dnf(self.formula, self.info, **kwargs)


        #After that we transform to a separated formula representation
        self.separated_formulas = SeparatedFormula.dnf_to_sf(self.dnf, **kwargs)


        #Finally, we calculate the TNF  
        self.tnf_formula = self.calculate_tnf(**kwargs)

        self.print_info()



            
    def print_info(self):
        """
        Print information about TNF, like TNF, result of verification TNF and another relative information stored in self.info dict
        """
        if self.activated_print_tnf:
            self.__print_tnf(self.tnf_formula)
        if self.activate_verification:
            print("Verifying DNF = TNF...")
            self.verification = self.verify()
            print("They are equivalent formulas", self.verification)
        if self.activated_print_info:
            print_info_map(self.info)


    
    @analysis
    def verify(self, **kwargs):
        """
        It verifies if TNF == DNF, for the equivalence be fulfilled the following preconditions must be fulfilled:
            - System variables must be deleted from  DNF and TNF formulas
            - Subsumption cant be applied neither in a particular move nor between moves

        
        """
        tnf_as_sf = self.tnf_to_separated_formulas(self.tnf_formula, **kwargs)
        are_equivalent = SeparatedFormula.are_equal_separated_formulas(self.separated_formulas, tnf_as_sf, env_minimal_covering=self.valid_env_valuations_ab, **kwargs)
        return are_equivalent


    @analysis
    def calculate_tnf(self, **kwargs):
        """
        Calculate TNF of given temporal formula
        """
        print("Calculating TNF...")
        tnf_formula = self.__tnf()        
        return tnf_formula


    
    @analysis
    def __print_tnf(self, tnf, **kwargs):
        """
        Print TNF
        """
        for key, value in tnf.items():
            print(key, ": ", len(value))
            for v in value:
                print("============>", v)

            print("\n")


    @staticmethod
    def print_tnf(tnf, **kwargs):
        """
        Print TNF
        """
        for key, value in tnf.items():
            print(key, ": ", len(value))
            for v in value:
                print("============>", v)

            print("\n")

                


    @analysis   
    def tnf_to_separated_formulas(self, tnf, **kwargs):
        """
        tnf_to_separated_formulas returns given tnf as a separated formula
        """
        separated_formulas = list()
        for key, values in tnf.items():
            for value in values:
                separated_formula = {'X':set(key), 'Y':value[0], 'Futures':value[1]}
                separated_formulas.append(separated_formula)
        return separated_formulas

    @analysis
    def __subtnf(self, formulas, **kwargs):

        """
        Given a list of separated formulas with same environment valuation, it calculates the TNF
        """        

        if not formulas:
            return [[{'False'}, [{'X[1]False'}]]]
        
        if len(formulas) == 1:
            return [[formulas[0]['Y'].copy(), formulas[0]['Futures'].copy()]]


        tnf = list() 
        skip = list() # Represent the list of literal sets already processed
        literals_stack = list() # Represent a stack of literal sets. Moreover, top of the stack represent the current set of literals
        futures_stack = list() # Represent a stack of list of futures sets. Moreover, top of the stack represent the current set of futures
        index_stack  = list() # El conjunto 

        index_stack.append(0) #Stack top indicates current formula that is pointing
        literals_stack.append(formulas[0]['Y'].copy())
        futures_stack.append(formulas[0]['Futures'].copy())

        i = 1 

        while i >= 0:

            literals_i = formulas[i]['Y'].copy()
            current_l = literals_stack[-1]

            if self.__is_consistent(current_l, literals_i, **kwargs):
                union_literals = current_l.union(literals_i)
                if self.__not_visited(union_literals, skip, **kwargs):
                    futures_i = formulas[i]['Futures'][0].copy()
                    if union_literals != current_l:
                        current_f = futures_stack[-1]
                        union_futures = current_f[:]
                        self.__append_future(union_futures, futures_i, **kwargs)

                        literals_stack.append(union_literals)
                        futures_stack.append(union_futures)
                        index_stack.append(i)
                    else:
                        current_f = futures_stack[-1]
                        self.__append_future(current_f, futures_i, **kwargs)


                    
            i += 1  

            if i == len(formulas):         
                move_literals = literals_stack.pop()
                move_futures = futures_stack.pop()
                

                if self.__can_be_inserted_to_tnf(move_literals, skip, **kwargs):
                    new_separated_formula = [move_literals, move_futures]
                    self.__append_tnf(tnf, new_separated_formula)
                skip.append(move_literals)

                possible_i = index_stack.pop() + 1

                i = TNF.get_valid_i(possible_i, formulas, index_stack, literals_stack, futures_stack, skip)     

        return tnf           

    @staticmethod
    def get_valid_i(i, formulas, index_stack, literals_stack, futures_stack, skip, recursive = True):
        """
        Given a concrete state of tnf algorithm (i, formulas, index_stack, literals_stack, futures_stack, skip), 
        get_valid_i returns a valid index i, we define valid index i as follows:
            - i < len(formulas) 
            - i == -1, if tnf algorithm is finished   
        """
        if recursive:
            return TNF.__get_valid_i_r(i, formulas, index_stack, literals_stack, futures_stack, skip)
        else:
            return TNF.__get_valid_i_i(i, formulas, index_stack, literals_stack, futures_stack, skip)


    @staticmethod
    def __get_valid_i_i(i, formulas, index_stack, literals_stack, futures_stack, skip):
        """
        Iterative version of get_valid_i
        """
        valid_i = False
        while not valid_i:
            if i == len(formulas) and index_stack:
                literals_stack.pop()
                futures_stack.pop()
                i = index_stack.pop() + 1
            elif i == len(formulas) and not index_stack:
                valid_i = True
            elif formulas[i]['Y'] in skip:
                i+=1
            elif  i < len(formulas) and not index_stack:
                valid_i = True
                index_stack.append(i)
                literals_stack.append(formulas[i]['Y'].copy())
                futures_stack.append(formulas[i]['Futures'].copy())
            else:
                valid_i = True
        return i

    @staticmethod
    def __get_valid_i_r(i, formulas, index_stack, literals_stack, futures_stack, skip):
        """
        Recursive version of get_valid_i
        """

        if i == len(formulas):
            if not index_stack: 
                # If there is no index to pop from index_stack, it means that all formulas have been visited and the algorithm must be end 
               return -1
            else:
                #Otherwise,  we pop an index from index_stack and we increment in 1. Moreover, possible_i  may not 
                # be a valid index due to i == len(formulas) or formulas[i]['Y'] in skip, so we call recusively to the function to ensure and generate a valid one.
                literals_stack.pop()
                futures_stack.pop()
                possible_i = index_stack.pop() + 1
                i = TNF.__get_valid_i_r(possible_i, formulas, index_stack, literals_stack, futures_stack, skip) 
                return i
        else:
            if formulas[i]['Y'] in skip:
                # if index i referes to a set of system variables contained in skip list, we increment in 1. Moreover, possible_i  may not 
                # be a valid index due to i == len(formulas) or formulas[i]['Y'] in skip, so we call recusively to the function to ensure and generate a valid one.
                possible_i = i + 1
                i = TNF.__get_valid_i_r(possible_i, formulas, index_stack, literals_stack, futures_stack, skip)
                return i
            elif not index_stack:
                # if i < len(formulas) and is not contained in skip list, it's a valid index. 
                # However, whether index_stack is empty we push:
                #   - i to index_stack
                #   - formulas[i]['Y'] to literals_stack
                #   - formulas[i]['Futures'] to futures_stack
                index_stack.append(i)
                literals_stack.append(formulas[i]['Y'].copy())
                futures_stack.append(formulas[i]['Futures'].copy())
                return i

            else:
                # if i < len(formulas) and is not contained in skip list, it's a valid index and as index stack is not empty, we only have to return i
                return i

                    

    def __append_tnf(self, tnf, new_move):
        """
        Append a new move to the tnf
        """
        if self.activate_verification:
            tnf.append(new_move)
        else:
            Subsumptions.move_lists_with_move(tnf, new_move)





    
    def __tnf(self):
        """
        we calculate the tnf as the conjunction of TNF of the formulas compatible with each evaluation of the environment.
        """
        tnf_formula = dict()  
        for env_move in self.valid_env_valuations:
            compatible_formulas = SeparatedFormula.get_separated_formula_compatibles_by_env(env_move, self.separated_formulas)
            env_move_compatibles_sub_tnf = self.__subtnf(compatible_formulas)
            tnf_formula[frozenset(env_move)] = env_move_compatibles_sub_tnf
        return tnf_formula
    
    @analysis
    def __can_be_inserted_to_tnf(self, possible_literals, skip, **kwargs):
    
        for skip_i in skip:
            if possible_literals <= skip_i:
                return False
        return True

    
    @analysis
    def __not_visited(self, union_literals, skip, **kwargs):
        """
        Given a list of literal sets (skip) and a set of literals (union_literals), return True if union_literals not in skip, otherwise, False
        """
        return not union_literals in skip

    @analysis
    def __is_consistent(self, set_literals_1, set_literals_2, **kwargs):
        """
        Given two sets of literals, return if the conjunction of the two sets is consistent, that's is, the resulting set does not contain any literal with it's negation.
        """
        if len(set_literals_1) < len(set_literals_2):
            for l in set_literals_1:
                if TemporalFormula.neg_literal(l, **kwargs) in set_literals_2:
                    return False
        else:
            for l in set_literals_2:
                if TemporalFormula.neg_literal(l, **kwargs) in set_literals_1:
                    return False
        return True

    
    @analysis

    def __append_future(self,union_futures, futures_i, **kwargs):
        """
        Given union_futures(a list of futures sets) and future_i (a futures set), return a list of sets 
        that represents the conjuction of union_futures and futures_i. If the verification of tnf is not activated, subsumptions
        will be applied, otherwise, whether future_i is not included in union_futures, it will be added.

        Args: 
            union_futures: List of sets
            future_i: set

        Returns:
            List of sets that represents the conjunction of union_futures and future_i

        """
        if self.activate_verification:
            if futures_i not in union_futures:
                union_futures.append(futures_i)
        else:
            Subsumptions.list_futures_set_with_futures_set(union_futures, futures_i)



    




