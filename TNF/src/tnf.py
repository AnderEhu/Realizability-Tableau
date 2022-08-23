
import copy
from operator import index

from traceback import print_tb
from Tableau.src.minimal_covering import MinimalCovering

from TemporalFormula.src.temporal_formula import AUX_NODE, NEG_AUX_NODE, OR_OPERATOR, TemporalFormula
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
                    info = dict(),
                    subsumptions = list(),
                    activated_apply_subsumptions = False, 
                    activated_print_info = True, 
                    activated_print_tnf = True,
                    activate_verification = True,
                    **kwargs):


        self.info = info
        self.is_consistent = dict()
        self.subsumptions = subsumptions
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
        self.env_vars = TemporalFormula.get_env_actual_variables(self.formula)
        self.all_env_valuations = TemporalFormula.get_all_assignments(self.env_vars,**kwargs)

        if env_constraints_str:
            self.env_constraints = TemporalFormula(env_constraints_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs).ab
            self.valid_env_valuations = TemporalFormula.calculate_dnf(self.env_constraints, **kwargs)
            self.valid_env_minimal_covering = TNF.get_env_minimal_covering(self.all_env_valuations, self.valid_env_valuations)
        else:
            self.valid_env_minimal_covering = self.all_env_valuations

        self.valid_env_minimal_covering_ab = TNF.env_covering_to_ab(self.valid_env_minimal_covering)



        # Next, the equvialent DNF of formula is calculated

        self.dnf = TemporalFormula.calculate_dnf(self.formula, self.info, **kwargs)
        self.all_futures = TemporalFormula.get_all_dnf_temporal_formulas(self.dnf, self.info, **kwargs)

        #After that we transform to a separated formula representation
        self.separated_formulas = SeparatedFormula.dnf_to_sf(self.dnf, **kwargs)

        #Finally, we calculate the TNF  
        self.tnf_formula = self.calculate_tnf(**kwargs)

        self.print_info()



            
    def print_info(self):
        if self.activated_print_tnf:
            self.__print_tnf(self.tnf_formula)
        if self.activate_verification:
            self.verification = self.verify()
        if self.activated_print_info:
            print_info_map(self.info)


    
    @analysis
    def verify(self, **kwargs):
        print("Verifying DNF = TNF...")
        are_equivalent = self.are_equal_tnf_and_separated_formulas(**kwargs)
        print("They are equivalent formulas", are_equivalent)
        return are_equivalent


    @analysis
    def calculate_tnf(self, **kwargs):
        print("Calculating TNF...")
        tnf_formula = self.__tnf()        
        return tnf_formula


    
    @analysis
    def __print_tnf(self, tnf, **kwargs):
        for key, value in tnf.items():
            print(key, ": ", len(value))
            for v in value:
                print("============>", v[0])
                for vi in v[1]:
                    print("============>", vi)
                print("\n")

            print("\n")




    @analysis
    def are_equal_tnf_and_separated_formulas(self, **kwargs):
        tnf_as_sf = self.tnf_to_separated_formulas(self.tnf_formula, **kwargs)

        return SeparatedFormula.are_equal_separated_formulas(self.separated_formulas, tnf_as_sf, env_minimal_covering=self.valid_env_minimal_covering_ab, **kwargs)

    @analysis   
    def tnf_to_separated_formulas(self, tnf, **kwargs):
        separated_formulas = list()
        for key, values in tnf.items():
            for value in values:
                separated_formula = {'X':set(key), 'Y':value[0], 'Futures':value[1]}
                separated_formulas.append(separated_formula)
        return separated_formulas

    @analysis
    def __tnf_step(self, formulas, **kwargs):
        formulas = copy.deepcopy(formulas)
        if not formulas:
            return [[{'False'}, [{'X[1]False'}]]]
        
        if len(formulas) == 1:
            return [[formulas[0]['Y'], formulas[0]['Futures']]]


        tnf, skip, literals_stack, futures_stack, index_stack  = list(), list(), list(), list(), list()

        index_stack.append(0)
        literals_stack.append(copy.deepcopy(formulas[0]['Y']))
        futures_stack.append(copy.deepcopy([formulas[0]['Futures'][0]]))

        i = 1

        while index_stack:
            assert len(futures_stack) == len(literals_stack) == len(index_stack)
            literals_i = copy.deepcopy(formulas[i]['Y'])
            current_l = copy.deepcopy(literals_stack[-1])

            if self.__is_consistent(current_l, literals_i, **kwargs):
                union_literals = self.__union(current_l,literals_i, **kwargs)
                if self.__not_visited(union_literals, skip, **kwargs):
                    futures_i = copy.deepcopy(formulas[i]['Futures'])
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
                valid_i = False
                while not valid_i:

                    if possible_i == len(formulas) and index_stack:
                        literals_stack.pop()
                        futures_stack.pop()
                        possible_i = index_stack.pop() + 1
                    if possible_i == len(formulas) and not index_stack:
                        break
                    elif formulas[possible_i]['Y'] in skip:
                        possible_i+=1
                    else:
                        i = possible_i
                        valid_i = True
                        if not index_stack:
                            index_stack.append(i)
                            literals_stack.append(copy.deepcopy(formulas[i]['Y']))
                            futures_stack.append(copy.deepcopy(formulas[i]['Futures']))

                        
        return tnf
                    

    def __append_tnf(self, tnf, new_separated_formula, delete_implicates = False):
        tnf_i_remove = list()
        if delete_implicates:
            separated_formula_ab = SeparatedFormula.separated_formula_strict_futures_to_ab(new_separated_formula[1])
            for i, sf_i in enumerate(tnf):
                sf_i_ab = SeparatedFormula.separated_formula_strict_futures_to_ab(sf_i[1])
                if TemporalFormula.is_implicated_strict_formulas(separated_formula_ab, sf_i_ab):
                    #print(separated_formula_ab, "IMPLIES", sf_i_ab, "\n")
                    return
                if TemporalFormula.is_implicated_strict_formulas(sf_i_ab, separated_formula_ab):
                    #print(sf_i_ab, "IMPLIES", separated_formula_ab, "\n")
                    tnf_i_remove.append(i)

                #print(sf_i_ab, "NOT IMPLIES", separated_formula_ab, "\n")
        if tnf_i_remove:   
            #print("tnf", tnf_i_remove)
            tnf = [f for i, f in enumerate(tnf) if i not in tnf_i_remove]



        tnf.append(new_separated_formula)



    
    def __tnf(self):
        tnf_formula = dict()   
        for env_move in self.valid_env_minimal_covering:
            compatible_formulas = SeparatedFormula.get_separated_formula_compatibles_by_env(env_move, self.separated_formulas)
            env_move_compatibles_sub_tnf = self.__tnf_step(compatible_formulas)
            tnf_formula[frozenset(env_move)] = env_move_compatibles_sub_tnf
        return tnf_formula
    
    @analysis
    def __can_be_inserted_to_tnf(self, possible_literals, skip, **kwargs):

        for skip_i in skip:
            if possible_literals <= skip_i:
                return False
        return True

    
    @analysis
    def __union(self, current_l, literals_i, **kwargs):
        union = current_l.union(literals_i)
        return union
    
    @analysis
    def __not_visited(self, a, l, **kwargs):
        return not a in l

    @analysis
    def __is_consistent(self, set_literals_1, set_literals_2, **kwargs):
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
        for future_i in futures_i:
            if future_i not in union_futures:
                union_futures.append(future_i)

    @staticmethod
    def env_covering_to_ab(env_covering):
        if not env_covering:
            return [OR_OPERATOR, AUX_NODE, NEG_AUX_NODE]
        env_covering_ab = ['|']
        for env_valuations in env_covering:
            for env_valuation in env_valuations:
                if TemporalFormula.is_neg(env_valuation[0]):
                    env_covering_ab.append(['-', env_valuation[1:]])
                else:
                    env_covering_ab.append(env_valuation)
        fix_env_covering_ab = TemporalFormula.fix_ab_list(env_covering_ab)
        return fix_env_covering_ab       



    @staticmethod
    def get_env_minimal_covering(all_assignments, valid_assignments):
        if not valid_assignments:
            return all_assignments
        env_minimal_covering = list()
        for assignment in all_assignments:
            if TNF.is_valid_assignment(assignment, valid_assignments):
                env_minimal_covering.append(assignment)
        return env_minimal_covering

    @staticmethod
    def is_valid_assignment(assignment, valid_assignments):
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

