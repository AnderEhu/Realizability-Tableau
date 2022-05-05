
import copy
import itertools

import time
import multiprocessing as mp
from multiprocessing.pool import ThreadPool as Pool

from analysis import calculate_analysis

from covering import get_env_minimal_covering

from temporal_formula import  dnf_to_sf, are_equal_formulas, calculate_dnf, calculate_subsumptions, empty_separated_formula, get_all_assignments, get_all_dnf_temporal_formulas, get_env_variables, get_neg_literal, get_variable, is_implicated, is_neg, is_var_env, neg_literal, neg_separated_formulas_to_ab, print_separated_formula, separated_formulas_to_ab, set_separated_formula
from tools import add_info, print_info

class TNF:
    def __init__(self, temporal_formula, 
                    env_vars,
                    env_minimal_covering = list(), 
                    info = dict(), 
                    activated_apply_subsumptions = False, 
                    activated_improved_stnf = True, 
                    activated_print_info = True, 
                    activated_calculate_analysis = False, 
                    activated_print_stnf = True,
                    activate_verification = True):


        self.formula = temporal_formula
        self.info = info
        self.env_minimal_covering = env_minimal_covering
        self.is_consistent = dict()
        self.env_vars = env_vars
        if not env_minimal_covering:
            self.env_minimal_covering = self.__get_all_assignments(self.env_vars)

        self.dnf = calculate_dnf(self.formula, self.info)
        self.all_futures = get_all_dnf_temporal_formulas(self.dnf, self.info)
        self.activated_improved_stnf = activated_improved_stnf
        self.activated_apply_subsumptions = activated_apply_subsumptions
        if activated_apply_subsumptions:
            self.subsumptions = calculate_subsumptions(self.all_futures, self.info)
        else:
            self.subsumptions = dict()
        
        self.separated_formulas = dnf_to_sf(self.dnf, self.subsumptions, self.env_vars)
        
        self.stnf_formula = self.calculate_stnf()

        
        if activated_print_stnf:
            self.__print_tnf(self.stnf_formula)
        if activate_verification:
            self.verify()
        if activated_print_info:
            print_info(self.info)
        if activated_calculate_analysis:
            calculate_analysis(self.info)
            

 

    def get_tnf(self):
        if self.tnf_formula:
            return self.tnf_formula
        return False

    def verify(self):
        print("Verifying DNF = TNF...")
        are_equivalent = self.are_equal_tnf_and_separated_formulas()
        add_info(self.info, "TNF = DNF(s): ", are_equivalent)
        return are_equivalent


   
          

    def calculate_tnf(self):
        print("Calculating TNF...")
        start = time.time()
        tnf_formula = self.tnf()
        add_info(self.info, "TNF(s): ", time.time()-start)
        add_info(self.info, "TNF = DNF(s): ", self.are_equal_tnf_and_separated_formulas())

        return tnf_formula

    def calculate_stnf(self):
        print("Calculating sTNF...")
        start = time.time()
        stnf_formula = self.stnf()
        add_info(self.info, "sTNF(s): ", time.time()-start)
        
        return stnf_formula
        

    def __hold_condition(self, literals_i, literals_j):
        if not literals_j or not literals_i:
            return False
        for literal_i in literals_i:
            neg_literal_i = get_neg_literal(literal_i)
            if neg_literal_i in literals_j:
                return True
        return False

    def __get_common_literals(self, literals_i, literals_j):
        return literals_i.intersection(literals_j)

    def __get_different_literals(self, literals_i, literals_j):
        return literals_i-literals_j, literals_j-literals_i

    def __dnf_literals(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, all = True):
        if all:
            return self.__dnf_literals_all(d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future)
        else:
            return self.__dnf_literals_alternative(d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future)



    def __dnf_literals_all(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future):
        negdj = neg_dj_X | neg_dj_Y
        if negdj == set():
            return False
        l = [False, True]
        negdj_assignment = self.__get_assignment(negdj) 
        assignments = set(itertools.product(l, repeat=len(negdj))) - negdj_assignment 
        res = list()
        for assignment in assignments:
            negdj_list = list(negdj)
            X = d_X | di_X
            Y = d_Y | di_Y
            for i, is_true in enumerate(assignment):
                var_i = get_variable(negdj_list[i])
                if is_true:
                    if is_var_env(var_i):
                        X.add(var_i)
                    else:
                        Y.add(var_i)
                else:
                    neg_literal_i = get_neg_literal(var_i)
                    if is_var_env(var_i):
                        X.add(neg_literal_i)
                    else:
                        Y.add(neg_literal_i)

            res.append(set_separated_formula(X, Y, future))
        return res

    def __dnf_literals_alternative(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future):
        if neg_dj_X == set() and neg_dj_Y == set():
            return False
        res = list()
    
        for literal in neg_dj_X:
            X = d_X | di_X
            Y = d_Y | di_Y
            X.add(neg_literal(literal))
            res.append(set_separated_formula(X, Y, future))

        for literal in neg_dj_Y:
            X = d_X | di_X
            Y = d_Y | di_Y
            Y.add(neg_literal(literal))
            res.append(set_separated_formula(X, Y, future))

        return res

    def __get_assignment(self, f):
        ass = list()
        for l in f:
            if l[0] == "-":
                ass.append(False)
            else:
                ass.append(True)
        return {tuple(ass)}


    def __apply_join_rule(self, sf1, sf2):
        d_X =  self.__get_common_literals(sf1['X'], sf2['X'])
        d_Y = self.__get_common_literals(sf1['Y'], sf2['Y'])
        d1_X, d2_X = self.__get_different_literals(sf1['X'], sf2['X'])
        d1_Y, d2_Y = self.__get_different_literals(sf1['Y'], sf2['Y'])
        if self.activated_apply_subsumptions:
            join_futures = self.__join_futures(sf1['Futures'], sf2['Futures'])
        else:
            join_futures = sf1['Futures'] + sf2['Futures']

        new_join_1 = set_separated_formula(d_X | d1_X | d2_X, d_Y | d1_Y | d2_Y, join_futures)
        new_join_2 = self.__dnf_literals(d_X, d_Y, d1_X, d1_Y, d2_X, d2_Y, sf1['Futures'])
        new_join_3 = self.__dnf_literals(d_X, d_Y, d2_X, d2_Y, d1_X, d1_Y, sf2['Futures'])
        return new_join_1, new_join_2, new_join_3

            
    def __join_futures(self, future1, future2):
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
    

    def tnf(self):
        formula = copy.deepcopy(self.separated_formulas)
        all_hold_condition = False
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    if not (self.__hold_condition(separated_formula_i['X'], separated_formula_j['X']) or self.__hold_condition(separated_formula_i['Y'], separated_formula_j['Y'])):
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(separated_formula_i, separated_formula_j)

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

    def __sub_tnf(self, env_move, compatibles, stnf_formula):
        formula = copy.deepcopy(compatibles)
        all_hold_condition = False
        if not formula:
            stnf_formula.append(set_separated_formula(env_move, set(), list()))
            return
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    if not self.__hold_condition(separated_formula_i['Y'], separated_formula_j['Y']):
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        separated_formula_i['X'] = set()
                        separated_formula_j['X'] = set()
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(separated_formula_i, separated_formula_j)

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
            stnf_formula.append(set_separated_formula(env_move, fi['Y'], fi['Futures']))
        


    

    def __print_tnf(self, tnf):
        for key, value in tnf.items():
            print(key, ": ", len(value))
            # for v in value:
            #     print("============>", v[0], v[1])
            print("\n")

    def __get_env_variables(self, separated_formulas):
        start = time.time()
        if "env_vars(s)" not in self.info:
            self.info['env_vars(s)'] = 0
        env_vars = get_env_variables(separated_formulas)
        self.info['env_vars(s)'] += (time.time()-start)
        return env_vars

    def __get_all_assignments(self, env_vars):
        start = time.time()
        if "All env assignments(s)" not in self.info:
            self.info['All env assignments(s)'] = 0
        all_assignments = get_all_assignments(env_vars)
        self.info['All env assignments(s)'] += (time.time()-start)
        return all_assignments

    def __calculate_dnf(self, formula):
        start = time.time()
        if "Constraints DNF(s)" not in self.info:
            self.info['Constraints DNF(s)'] = 0
        dnf = calculate_dnf(formula)
        print(dnf)
        self.info['Constraints DNF(s)'] += (time.time()-start)
        return dnf

    def __get_env_minimal_covering(self, all_assignments, valid_assignments):
        start = time.time()
        if "Valid covering(s)" not in self.info:
            self.info['Valid covering(s)'] = 0
        valid_covering = get_env_minimal_covering(all_assignments, valid_assignments)
        self.info['Valid covering(s)'] += (time.time()-start)
        return valid_covering


    


    def __get_separated_formula_compatibles_by_env(self, env_move, separated_formulas):
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


    def are_equal_tnf_and_separated_formulas(self):
        tnf_as_sf = self.tnf_to_separated_formulas(self.stnf_formula)
        return are_equal_formulas(self.separated_formulas, tnf_as_sf)

        
    def tnf_to_separated_formulas(self, tnf):
        separated_formulas = list()
        for key, values in tnf.items():
            for value in values:
                separated_formula = {'X':set(key), 'Y':value[0], 'Futures':value[1]}
                separated_formulas.append(separated_formula)
        return separated_formulas


    def __stnf_step(self, formulas):
        
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

            if self.__is_consistent(current_l, literals_i):
                union_literals = self.__union(current_l,literals_i)
                if self.__not_visited(union_literals, skip):
                    current_f = futures_stack[-1]
                    futures_i = formulas[i]['Futures']
                    if union_literals != current_l:

                        literals_stack.append(union_literals)

                        if current_f != [{'False'}]:  
                            union_futures = current_f[:]
                            self.__append_future(union_futures, futures_i[0])
                            futures_stack.append(union_futures)
                        else:
                            futures_stack.append([futures_i[0]])
                        if i < max_i:
                            index_stack.append(i+1)
                        
                        
                    else:
                        if futures_i == [set()]:
                            futures_stack = [{'True'}]
                        elif current_f != [{'False'}]:
                            self.__append_future(current_f, futures_i[0])
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
                        if self.__insert_to_stnf(move_literals, skip):
                            stnf.append(new_separated_formula)
                    skip.append(move_literals)
                    
                    

        return stnf

    def stnf(self):
        stnf_formula = dict()   
        
        if not self.env_minimal_covering:
            self.__stnf_step(set(), self.separated_formulas, stnf_formula)

        else:
            for env_move in self.env_minimal_covering:
                compatible_formulas = self.__get_separated_formula_compatibles_by_env(env_move, self.separated_formulas)
                if self.activated_improved_stnf:
                    env_move_compatibles_sub_tnf = self.__stnf_step(compatible_formulas)
                    stnf_formula[frozenset(env_move)] = env_move_compatibles_sub_tnf
                else:
                    self.__sub_tnf(env_move, compatible_formulas, stnf_formula)
        return stnf_formula

    def __insert_to_stnf(self, possible_literals, skip):
        start = time.time()
        if "insert to tnf(s)" not in self.info:
            self.info['insert to tnf(s)'] = 0
        for skip_i in skip:
            if possible_literals <= skip_i:
                self.info['insert to tnf(s)'] += (time.time()-start)
                return False
        self.info['insert to tnf(s)'] += (time.time()-start)
        return True


    def __symmetric_difference(self, current_l, literals_i):
        start = time.time()
        if "symmetric_difference (s)" not in self.info:
            self.info['symmetric_difference (s)'] = 0
        diff = current_l.symmetric_difference(literals_i)
        self.info['symmetric_difference (s)'] += (time.time()-start)
        return diff

    def __union(self, current_l, literals_i):
        #start = time.time()
        #if "union (s)" not in self.info:
            #self.info['union (s)'] = 0
        union = current_l.union(literals_i)
        #self.info['union (s)'] += (time.time()-start)
        return union

    # def __insert_to_stnf(self, env_move, new_move, stnf):
    #         if new_move in stnf:
    #             return
    #         if [{"True"}] == new_move[1]:
    #             new_move[1] = [set()]
    #         remove_list = list()
    #         subsumed = False
    #         for move in stnf:
    #             if move[0] == new_move[0] or move[0] > new_move[0] or move[0] < new_move[0]:
    #                 if self.__has_weaker_futures(move, new_move):
    #                     subsumed = True
    #                     break

    #                 if self.__has_weaker_futures(new_move, move):
    #                     remove_list.append(move)
    #         if not subsumed:
    #             for m in remove_list:
    #                 stnf.remove(m)
    #             stnf.append(set_separated_formula(env_move, new_move[0], new_move[1]))

    def __has_weaker_futures(self, move1, move2):
        if move1 == move2:
            return True
        for future_2_i in move2[1]:
            subsumed = False
            for future_1_i in move1[1]:
                if self.__futures_set_subsumption(future_1_i, future_2_i):
                    subsumed  = True
                    break
            if not subsumed:
                return False
        return True

    def __not_visited(self, a, l):
        #start = time.time()
        #if "not_visited (s)" not in self.info:
            #self.info["not_visited (s)"] = 0
            
        #self.info["not_visited (s)"] += (time.time()-start)
        return not a in l


    def __is_consistent(self, set_literals_1, set_literals_2):
        #start = time.time()
        #if "is_consistent (s)" not in self.info:
            #self.info['is_consistent (s)'] = 0
        if len(set_literals_1) < len(set_literals_2):
            for l in set_literals_1:
                if neg_literal(l) in set_literals_2:
                    #self.info['is_consistent (s)'] += (time.time()-start)
                    return False
        else:
            for l in set_literals_2:
                if neg_literal(l) in set_literals_1:
                    #self.info['is_consistent (s)'] += (time.time()-start)
                    return False
        #self.info['is_consistent (s)'] += (time.time()-start)
        return True

    def __futures_set_subsumption(self, set1, set2):
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

    def __append_future(self,union_futures, futures_i):
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



    

