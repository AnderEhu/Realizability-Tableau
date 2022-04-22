
import copy
import csv
import itertools
import random
import sys
import time

from utils import utils
from run_bica import prime_cover_via_BICA
from collections import deque

class TNF:
    def __init__(self, parse_formulas, flines = False):
        
        self.__set_initial_parameters(parse_formulas)
        self.calculate_dnf()
        self.calculate_subsumptions()
        self.post_processing_bica_models()
        self.get_env_vars()
        self.calculate_tnf()
        self.calculate_verifications()
        if flines:
           self.info['Lines'] = flines
           self.calculate_analysis()
        #self.__print_tnf()
        self.__print_info()
        

    def get_tnf(self):
        if self.tnf_formula:
            return self.tnf_formula
        return False
        
    def __set_initial_parameters(self, parse_formulas):
        print("Initializing parameters..")
        self.start = time.time()
        self.info = dict()
        self.parse_formulas = parse_formulas     
              

    def calculate_tnf(self):
        print("Calculating TNF...")
        start = time.time()
        self.tnf_formula = self.tnf()
        self.__add_time(start, "TNF(s)")
        self.__add_info("TNF Length", len(self.tnf_formula))
        

    def calculate_dnf(self):
        print("Calculating DNF...")
        start = time.time()
        self.dnf_bica = prime_cover_via_BICA(self.parse_formulas)
        self.info['BICA(s)'] = round(time.time()-start, 6) 
        self.info['BICA Length'] = len(self.dnf_bica)


    def calculate_subsumptions(self):
        print("Calculating Subsumptions...")
        start = time.time()
        self.subsumptions = utils.calculate_subsumptions(self.dnf_bica)
        self.info['SUBSUMPTIONS(s)'] = round(time.time()-start, 6)
        self.info['SUBSUMPTIONS Length'] = len(self.subsumptions)


    def post_processing_bica_models(self):
        print("Post-Processing bica models...")
        start = time.time()
        self.formula = utils.post_processing_bica_models(self.dnf_bica, self.subsumptions)
        self.info['POST-PROCESSING MODELS(s)'] = round(time.time()-start, 6) 
        self.info['POST-PROCESSING MODELS Length'] = len(self.formula)

    def get_env_vars(self):
        start = time.time()
        self.env_vars = utils.get_X(self.formula)
        self.info['ENV VARS(s)'] = round(time.time()-start, 6) 
        self.info['ENV VARS Length'] = len(self.env_vars)
        


    def calculate_verifications(self):
        start = time.time()
        self.is_dnf_equal_tnf = utils.is_dnf_equal_tnf(self.formula, self.tnf_formula)
        self.__add_time(start, "VERIFICATION(s)")
        self.__add_info("DNF = TNF",  self.is_dnf_equal_tnf)

    def __print_tnf(self):
        print("\n=========================== TNF ===========================\n")
        print(utils.print_separated_formula(self.tnf_formula))
        print("\n=========================== TNF ===========================\n")




    def __print_info(self):
        print("=========================== INFO ===========================\n")
        for key, value in self.info.items():
            print(">>", key, ": ", value, "\n")        
        print(">>", "TOTAL(s)", ": ", time.time()-self.start, "\n")
        print("=========================== INFO ===========================")
    def calculate_analysis(self):
        with open("analysis_TNF.csv", 'a') as f:
            w = csv.DictWriter(f, self.info.keys())
            #w.writeheader()
            w.writerow(self.info)
        #self.__write_csv(flines, len(self.formula), self.tnf_time, len(self.tnf_formula), self.short_tnf_time, len(self.short_tnf_res), self.dnf_tnf_verification, self.tnf_to_stnf_verification, "analysis_TNF.csv")

    def __write_csv(self, f, DNF_len, TNF_Time, TNF_length, sTNF_time, sTNF_length, TNF_equal_DNF, sTNF_implies_TNF, path):

        row =  [f, DNF_len, TNF_Time, TNF_length, sTNF_time, sTNF_length, TNF_equal_DNF, sTNF_implies_TNF]
        # open the file in the write mode
        with open(path, mode='a') as f:
            writer = csv.writer(f, delimiter=',')
            # write a row to the csv file
            writer.writerow(row)

        # close the file
        f.close()

    def __add_info(self, key, value):
        self.info[key] = value

    def __add_time(self, start, strTime):
        s = time.time()-start
        self.__add_info(strTime, round(s, 6))
        self.currentTime = time.time() 

    def __literals(self, separated_formula):
        return separated_formula[0]

    def __future_formulas(self, separated_formula):
        return separated_formula[1]

    def __hold_condition(self, literals_i, literals_j):
        for literal_i in literals_i:
            neg_literal_i = utils.get_neg_literal(literal_i)
            if neg_literal_i in literals_j:
                return True
        return False

    def __get_common_literals(self, literals_i, literals_j):
        return literals_i.intersection(literals_j)

    def __get_different_literals(self, literals_i, literals_j):
        return literals_i-literals_j, literals_j-literals_i

    def __dnf_literals(self, d, di, negdj, future, all = True):
        if all:
            return self.__dnf_literals_all(d, di, negdj, future)
        else:
            return self.__dnf_literals_alternative(d, di, negdj, future)


    def __dnf_literals_all(self, d, di, negdj, future):
        if negdj == set():
            return False
        l = [False, True]
        negdj_assigment = self.__get_assigment(negdj) 
        assigments = set(itertools.product(l, repeat=len(negdj))) - negdj_assigment 
        res = list()
        for assigment in assigments:
            negdj_dnf = set()
            negdj_list = list(negdj)
            for i, is_true in enumerate(assigment):
                var_i = utils.get_variable(negdj_list[i])
                if is_true:
                    negdj_dnf.add(var_i)
                else:
                    neg_literal_i = utils.get_neg_literal(var_i)
                    negdj_dnf.add(neg_literal_i)

            res.append([d.union(di).union(negdj_dnf), future])
        return res

    def __dnf_literals_alternative(self, d, di, negdj, future):
        if negdj == set():
            return False
        res = list()
    
        for literal in list(negdj):
            neg_literal = {utils.neg_literal(literal)}
            res.append([d.union(di).union(neg_literal), future])
        return res

    def __get_assigment(self, f):
        ass = list()
        for l in f:
            if l[0] == "-":
                ass.append(False)
            else:
                ass.append(True)
        return {tuple(ass)}


    def __apply_join_rule(self, literals_i, literals_j, future_formulas_i, future_formulas_j):
        d =  self.__get_common_literals(literals_i, literals_j)
        d1, d2 = self.__get_different_literals(literals_i, literals_j)
        join_futures = self.__join_futures(future_formulas_i, future_formulas_j)
        new_join_1 = [d.union(d1).union(d2), join_futures]
        if future_formulas_i == [{"True"}]:
            future_formulas_i = [set()]
        if future_formulas_j == [{"True"}]:
            future_formulas_j = [set()]
        new_join_2 = self.__dnf_literals(d, d1, d2, future_formulas_i)
        new_join_3 = self.__dnf_literals(d, d2, d1, future_formulas_j)
        return new_join_1, new_join_2, new_join_3
            
    def __join_futures(self, future1, future2):
        if future1 == [set()] or future2 == [set()]:
            return [set()]
        if future1 == [{"True"}] or future2 == [{"True"}]:
            return [set()]
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
        formula = copy.deepcopy(self.formula)
        print(formula)
        all_hold_condition = False
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    
                    literals_i = self.__literals(separated_formula_i)
                    literals_j =  self.__literals(separated_formula_j)
                    if not self.__hold_condition(literals_i, literals_j):
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        future_formulas_i = self.__future_formulas(separated_formula_i)
                        future_formulas_j =  self.__future_formulas(separated_formula_j)
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(literals_i, literals_j, future_formulas_i, future_formulas_j)

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

    def are_all_futures_in(self, f1, f2):
        #f1 in f2
        for f1_i in f1:
            if f1_i not in f2:
                return False
        return True         

    def __delete_system_vars(self, literals):
        res = set()
        for l in literals:
            if utils.is_var_env(l):
                res.add(l)
        return res