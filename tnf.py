
import copy
import itertools

import time
import multiprocessing as mp
from multiprocessing.pool import ThreadPool as Pool

from analysis import calculate_analysis
from temporal_formula import TemporalFormula
from tools import add_info, print_info, analysis

class TNF:
    def __init__(self, temporal_formula, 
                    env_vars,
                    env_minimal_covering = list(), 
                    info = dict(), 
                    activated_apply_subsumptions = False, 
                    activated_improved_stnf = True, 
                    activated_print_info = False, 
                    activated_calculate_analysis = False, 
                    activated_print_stnf = False,
                    activate_verification = False,
                    **kwargs):


        self.formula = temporal_formula
        self.info = info
        self.env_minimal_covering = env_minimal_covering
        self.is_consistent = dict()
        self.env_vars = env_vars
        if not env_minimal_covering:
            self.env_minimal_covering = self.__get_all_assignments(self.env_vars,**kwargs)

        self.dnf = TemporalFormula.calculate_dnf(self.formula, self.info, **kwargs)
        self.all_futures = TemporalFormula.get_all_dnf_temporal_formulas(self.dnf, self.info, **kwargs)
        self.activated_improved_stnf = activated_improved_stnf
        self.activated_apply_subsumptions = activated_apply_subsumptions
        if activated_apply_subsumptions:
            exit()
            #self.subsumptions = calculate_subsumptions(self.all_futures, self.info)
        else:
            self.subsumptions = dict()
        
        self.separated_formulas = TemporalFormula.dnf_to_sf(self.dnf, self.subsumptions, self.env_vars, **kwargs)

        
        self.stnf_formula = self.calculate_stnf(**kwargs)

        
        if activated_print_stnf:
            self.__print_tnf(self.stnf_formula, **kwargs)
        if activate_verification:
            self.verify(**kwargs)
        if activated_print_info:
            print_info(self.info, **kwargs)
        if activated_calculate_analysis:
            calculate_analysis(self.info, **kwargs)
            
    @analysis
    def is_not_X_covering(self, **kwargs):
        for _, value in self.stnf_formula.items():
            if value == list():
                return True
        return False

    @analysis
    def get_tnf(self, **kwargs):
        if self.tnf_formula:
            return self.tnf_formula
        return False
    
    @analysis
    def verify(self, **kwargs):
        print("Verifying DNF = TNF...")
        are_equivalent = self.are_equal_tnf_and_separated_formulas(**kwargs)
        add_info(self.info, "TNF = DNF(s): ", are_equivalent)
        return are_equivalent

    @analysis
    def calculate_tnf(self, **kwargs):
        print("Calculating TNF...")
        start = time.time()
        tnf_formula = self.tnf(**kwargs)
        add_info(self.info, "TNF(s): ", time.time()-start)
        add_info(self.info, "TNF = DNF(s): ", self.are_equal_tnf_and_separated_formulas(**kwargs))

        return tnf_formula

    @analysis
    def calculate_stnf(self, **kwargs):
        print("Calculating sTNF...")
        start = time.time()
        stnf_formula = self.stnf(**kwargs)
        add_info(self.info, "sTNF(s): ", time.time()-start)
        
        return stnf_formula
        
    
    @analysis
    def __hold_condition(self, literals_i, literals_j, **kwargs):
        if not literals_j or not literals_i:
            return False
        for literal_i in literals_i:
            neg_literal_i = TemporalFormula.get_neg_literal(literal_i, **kwargs)
            if neg_literal_i in literals_j:
                return True
        return False
    
    @analysis
    def __get_common_literals(self, literals_i, literals_j, **kwargs):
        return literals_i.intersection(literals_j)
    
    @analysis
    def __get_different_literals(self, literals_i, literals_j, **kwargs):
        return literals_i-literals_j, literals_j-literals_i
    
    @analysis
    def __dnf_literals(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, all = True, **kwargs):
        if all:
            return self.__dnf_literals_all(d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, **kwargs)
        else:
            return self.__dnf_literals_alternative(d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, **kwargs)


    
    @analysis
    def __dnf_literals_all(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, **kwargs):
        negdj = neg_dj_X | neg_dj_Y
        if negdj == set():
            return False
        l = [False, True]
        negdj_assignment = self.__get_assignment(negdj, **kwargs) 
        assignments = set(itertools.product(l, repeat=len(negdj))) - negdj_assignment 
        res = list()
        for assignment in assignments:
            negdj_list = list(negdj)
            X = d_X | di_X
            Y = d_Y | di_Y
            for i, is_true in enumerate(assignment):
                var_i = TemporalFormula.get_variable(negdj_list[i], **kwargs)
                if is_true:
                    if TemporalFormula.is_var_env(var_i, **kwargs):
                        X.add(var_i)
                    else:
                        Y.add(var_i)
                else:
                    neg_literal_i = TemporalFormula.get_neg_literal(var_i, **kwargs)
                    if TemporalFormula.is_var_env(var_i, **kwargs):
                        X.add(neg_literal_i)
                    else:
                        Y.add(neg_literal_i)

            res.append(TemporalFormula.set_separated_formula(X, Y, future, **kwargs))
        return res
    
    @analysis
    def __dnf_literals_alternative(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, **kwargs):
        if neg_dj_X == set() and neg_dj_Y == set():
            return False
        res = list()
    
        for literal in neg_dj_X:
            X = d_X | di_X
            Y = d_Y | di_Y
            X.add(TemporalFormula.neg_literal(literal, **kwargs))
            res.append(TemporalFormula.set_separated_formula(X, Y, future, **kwargs))

        for literal in neg_dj_Y:
            X = d_X | di_X
            Y = d_Y | di_Y
            Y.add(TemporalFormula.neg_literal(literal, **kwargs))
            res.append(TemporalFormula.set_separated_formula(X, Y, future, **kwargs))

        return res
    
    @analysis
    def __get_assignment(self, f, **kwargs):
        ass = list()
        for l in f:
            if l[0] == "-":
                ass.append(False)
            else:
                ass.append(True)
        return {tuple(ass)}

    
    @analysis
    def __apply_join_rule(self, sf1, sf2, **kwargs):
        d_X =  self.__get_common_literals(sf1['X'], sf2['X'], **kwargs)
        d_Y = self.__get_common_literals(sf1['Y'], sf2['Y'], **kwargs)
        d1_X, d2_X = self.__get_different_literals(sf1['X'], sf2['X'], **kwargs)
        d1_Y, d2_Y = self.__get_different_literals(sf1['Y'], sf2['Y'], **kwargs)
        if self.activated_apply_subsumptions:
            join_futures = self.__join_futures(sf1['Futures'], sf2['Futures'], **kwargs)
        else:
            join_futures = sf1['Futures'] + sf2['Futures']

        new_join_1 = TemporalFormula.set_separated_formula(d_X | d1_X | d2_X, d_Y | d1_Y | d2_Y, join_futures, **kwargs)
        new_join_2 = self.__dnf_literals(d_X, d_Y, d1_X, d1_Y, d2_X, d2_Y, sf1['Futures'])
        new_join_3 = self.__dnf_literals(d_X, d_Y, d2_X, d2_Y, d1_X, d1_Y, sf2['Futures'])
        return new_join_1, new_join_2, new_join_3

    @analysis          
    def __join_futures(self, future1, future2, **kwargs):
        if future1 == [set()] or future2 == [set()]:
            return [set()]
        if future1 == [{"True"}] or future2 == [{"True"}]:
            return [{"True"}]
        join_f = copy.copy(future1)
        for f2 in future2:
            added = False
            for f1 in future1:
                if f1 > f2 and f1 != set() and f2 != set():
                    if f1 in join_f:
                        join_f.remove(f1)
                    join_f.append(f2)
                    added = True
                elif f1 == f2:
                    added = True
                else:
                    continue
            if not added and f2!= set():    
                join_f.append(f2)
        return join_f
    
    @analysis
    def tnf(self, **kwargs):
        formula = copy.deepcopy(self.separated_formulas)
        all_hold_condition = False
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    if not (self.__hold_condition(separated_formula_i['X'], separated_formula_j['X'], **kwargs) or self.__hold_condition(separated_formula_i['Y'], separated_formula_j['Y'], **kwargs)):
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(separated_formula_i, separated_formula_j, **kwargs)

                        formula.append(new_sf_1)
                        if new_sf_2:
                            for new_sf_2_i in new_sf_2:
                                formula.append(new_sf_2_i)
                        if new_sf_3:
                            for new_sf_3_i in new_sf_3:
                                formula.append(new_sf_3_i)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                all_hold_condition = True
        return formula
    
    @analysis
    def __sub_tnf(self, env_move, compatibles, stnf_formula, **kwargs):
        formula = copy.deepcopy(compatibles)
        all_hold_condition = False
        if not formula:
            stnf_formula.append(TemporalFormula.set_separated_formula(env_move, set(), list(), **kwargs))
            return
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    if not self.__hold_condition(separated_formula_i['Y'], separated_formula_j['Y'], **kwargs):
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        separated_formula_i['X'] = set()
                        separated_formula_j['X'] = set()
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(separated_formula_i, separated_formula_j, **kwargs)

                        formula.append(new_sf_1)
                        if new_sf_2:
                            for new_sf_2_i in new_sf_2:
                                formula.append(new_sf_2_i)
                        if new_sf_3:
                            for new_sf_3_i in new_sf_3:
                                formula.append(new_sf_3_i)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                all_hold_condition = True

        for fi in formula:
            stnf_formula.append(TemporalFormula.set_separated_formula(env_move, fi['Y'], fi['Futures'], **kwargs))
        


    
    @analysis
    def __print_tnf(self, tnf, **kwargs):
        print(tnf)
        for key, value in tnf.items():
            print(key, ": ", len(value))
            for v in value:
                print("============>", v[0])
                for vi in v[1]:
                    print("============>", vi)

            print("\n")

    @analysis
    def __get_all_assignments(self, env_vars, **kwargs):
        start = time.time()
        if "All env assignments(s)" not in self.info:
            self.info['All env assignments(s)'] = 0
        all_assignments = TemporalFormula.get_all_assignments(env_vars, **kwargs)
        self.info['All env assignments(s)'] += (time.time()-start)
        return all_assignments
    
    @analysis
    def __calculate_dnf(self, formula, **kwargs):
        start = time.time()
        if "Constraints DNF(s)" not in self.info:
            self.info['Constraints DNF(s)'] = 0
        dnf = TemporalFormula.calculate_dnf(formula, **kwargs)
        self.info['Constraints DNF(s)'] += (time.time()-start)
        return dnf



    @analysis
    def __get_separated_formula_compatibles_by_env(self, env_move, separated_formulas, **kwargs):
        #start = time.time()
        #if "compatibles(s)" not in self.info:
            #self.info['compatibles(s)'] = 0
        compatibles = list()
        for sf in separated_formulas:
            env_sf = sf['X']
            if env_sf <= env_move:
                compatibles.append(sf)
        #self.info['compatibles(s)'] += (time.time()-start)
        return compatibles

    @analysis
    def are_equal_tnf_and_separated_formulas(self, **kwargs):
        tnf_as_sf = self.tnf_to_separated_formulas(self.stnf_formula, **kwargs)
        return TemporalFormula.are_equal_formulas(self.separated_formulas, tnf_as_sf, **kwargs)

    @analysis   
    def tnf_to_separated_formulas(self, tnf, **kwargs):
        separated_formulas = list()
        for key, values in tnf.items():
            for value in values:
                separated_formula = {'X':set(key), 'Y':value[0], 'Futures':value[1]}
                separated_formulas.append(separated_formula)
        return separated_formulas

    @analysis
    def __stnf_step(self, formulas, **kwargs):
        
        if not formulas:
            return list()


        stnf, skip, literals_stack, futures_stack, index_stack  = list(), list(), list(), list(), list()

        literals_stack.append(set())
        futures_stack.append([{'False'}])
        index_stack.append(0)

        i = index_stack[0]
        max_i = len(formulas) - 1

        while index_stack:

            literals_i = formulas[i]['Y']
            current_l = literals_stack[-1]

            if self.__is_consistent(current_l, literals_i, **kwargs):
                union_literals = self.__union(current_l,literals_i, **kwargs)
                if self.__not_visited(union_literals, skip, **kwargs):
                    current_f = futures_stack[-1]
                    futures_i = formulas[i]['Futures']
                    if union_literals != current_l:

                        literals_stack.append(union_literals)

                        if current_f != [{'False'}]:  
                            union_futures = current_f[:]
                            self.__append_future(union_futures, futures_i[0], **kwargs)
                            futures_stack.append(union_futures)
                        else:
                            futures_stack.append([futures_i[0]])
                        if i < max_i:
                            index_stack.append(i+1)
                        
                        
                    else:
                        if futures_i == [set()]:
                            futures_stack = [{'True'}]
                        elif current_f != [{'False'}]:
                            self.__append_future(current_f, futures_i[0], **kwargs)
                        else:
                            futures_stack.pop()
                            futures_stack.append([futures_i[0]])
                    
            i += 1            
            if i >= len(formulas):
                i = index_stack.pop()  
                move_literals = literals_stack.pop()
                move_futures = futures_stack.pop()
                if move_futures != [{'False'}]:
                    new_separated_formula = [move_literals, move_futures]
                    if not skip:
                        skip.append(set())
                        stnf.append(new_separated_formula)
                    else:
                        if self.__insert_to_stnf(move_literals, skip, **kwargs):
                            stnf.append(new_separated_formula)
                    skip.append(move_literals)
                    
                    

        return stnf
    
    @analysis
    def stnf(self, **kwargs):
        stnf_formula = dict()   
        
        for env_move in self.env_minimal_covering:
            compatible_formulas = self.__get_separated_formula_compatibles_by_env(env_move, self.separated_formulas, **kwargs)
            if self.activated_improved_stnf:
                env_move_compatibles_sub_tnf = self.__stnf_step(compatible_formulas, **kwargs)
                stnf_formula[frozenset(env_move)] = env_move_compatibles_sub_tnf
            else:
                self.__sub_tnf(env_move, compatible_formulas, stnf_formula, **kwargs)
        return stnf_formula
    
    @analysis
    def __insert_to_stnf(self, possible_literals, skip, **kwargs):
        start = time.time()
        if "insert to tnf(s)" not in self.info:
            self.info['insert to tnf(s)'] = 0
        for skip_i in skip:
            if possible_literals <= skip_i:
                self.info['insert to tnf(s)'] += (time.time()-start)
                return False
        self.info['insert to tnf(s)'] += (time.time()-start)
        return True

    @analysis
    def __symmetric_difference(self, current_l, literals_i, **kwargs):
        start = time.time()
        if "symmetric_difference (s)" not in self.info:
            self.info['symmetric_difference (s)'] = 0
        diff = current_l.symmetric_difference(literals_i)
        self.info['symmetric_difference (s)'] += (time.time()-start)
        return diff
    
    @analysis
    def __union(self, current_l, literals_i, **kwargs):
        #start = time.time()
        #if "union (s)" not in self.info:
            #self.info['union (s)'] = 0
        union = current_l.union(literals_i)
        #self.info['union (s)'] += (time.time()-start)
        return union
    
    @analysis
    def __has_weaker_futures(self, move1, move2, **kwargs):
        if move1 == move2:
            return True
        for future_2_i in move2[1]:
            subsumed = False
            for future_1_i in move1[1]:
                if self.__futures_set_subsumption(future_1_i, future_2_i, **kwargs):
                    subsumed  = True
                    break
            if not subsumed:
                return False
        return True
    
    @analysis
    def __not_visited(self, a, l, **kwargs):
        #start = time.time()
        #if "not_visited (s)" not in self.info:
            #self.info["not_visited (s)"] = 0
            
        #self.info["not_visited (s)"] += (time.time()-start)
        return not a in l

    @analysis
    def __is_consistent(self, set_literals_1, set_literals_2, **kwargs):
        #start = time.time()
        #if "is_consistent (s)" not in self.info:
            #self.info['is_consistent (s)'] = 0
        if len(set_literals_1) < len(set_literals_2):
            for l in set_literals_1:
                if TemporalFormula.neg_literal(l, **kwargs) in set_literals_2:
                    #self.info['is_consistent (s)'] += (time.time()-start)
                    return False
        else:
            for l in set_literals_2:
                if TemporalFormula.neg_literal(l, **kwargs) in set_literals_1:
                    #self.info['is_consistent (s)'] += (time.time()-start)
                    return False
        #self.info['is_consistent (s)'] += (time.time()-start)
        return True
    
    @analysis
    def __futures_set_subsumption(self, set1, set2, **kwargs):
        #set1 subsumes set2
        if set1 == {'True'}:
            return True
        if set2 == {'True'}:
            return False
        for future2 in set2:
            future2_is_subsumed = False
            for future1 in set1:
                if future1 == future2 or (future1 in self.subsumptions and future2 in self.subsumptions[future1]):
                    future2_is_subsumed = True
                    break
            if not future2_is_subsumed:
                return False
        return True
    
    @analysis
    def __append_future(self,union_futures, futures_i, **kwargs):
        #start = time.time()
        #if "append future" not in self.info:
            #self.info['append future'] = 0
        if union_futures == [{'True'}] or futures_i == {'False'}:
            return
        elif futures_i == {'True'}:
            union_futures = list()
        else:
            union_futures.append(futures_i)
            #self.info['append future'] += (time.time()-start)

    @analysis
    def get_all_minimal_X_coverings(self, **kwargs):
        
        assignments_last_index = self.get_assignments_last_indices(self.stnf_formula, **kwargs)

        actual_minimal_covering_indexes = list(itertools.repeat ( 0, len(self.stnf_formula)))

        all_minimal_X_coverings = list()

        increment_index = 0

        while increment_index < len(self.stnf_formula):
            actual_minimal_covering = dict()
            for i, value_i in enumerate(actual_minimal_covering_indexes):
            
                assignment_i = frozenset(self.env_minimal_covering[i])
                actual_minimal_covering[assignment_i] = self.stnf_formula[assignment_i][value_i]

            all_minimal_X_coverings.append(actual_minimal_covering)
            
      
            while increment_index < len(self.stnf_formula) and actual_minimal_covering_indexes[increment_index] >= assignments_last_index[increment_index]:
                increment_index+=1

            if increment_index < len(self.stnf_formula) and actual_minimal_covering_indexes[increment_index] < assignments_last_index[increment_index]:
                actual_minimal_covering_indexes[increment_index] += 1
        
        return all_minimal_X_coverings
        
    @analysis
    def  get_assignments_last_indices(self, tnf, **kwargs):
        res = list()
        for _, value in tnf.items():
            res.append(len(value)-1)

        return res





    

