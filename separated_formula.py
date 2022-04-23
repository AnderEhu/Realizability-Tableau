


from temporal_formula import TemporalFormula, is_var_env, simple_formula_ab, simple_negation_ab
from subsumption import subsumes
from verifications import is_sat


def model_to_separated_formula(model, subsumptions):
    """
        Return a model in separated formula format
    """
    sf = empty_separated_formula()
    
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

def calculate_separated_formulas(dnf, subsumptions):
    processing_models = []
    for model in dnf:
        to_sf = model_to_separated_formula(model, subsumptions)
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
    neg_sf2__ab = neg_separated_formulas_to_ab(sf2)
    sf1_ab = separated_formulas_to_ab(sf1)
    sf2_ab = separated_formulas_to_ab(sf2)
    f1toAB = ['&', sf2_ab, neg_sf1_ab]
    f2toAB = ['&', sf1_ab, neg_sf2__ab]

    if not is_sat(f1toAB) or not is_sat(f2toAB):
        return False
    else:
        return True


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
    literals = separated_formula['X'] |  separated_formula['Y']
    futures = separated_formula['Futures']
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


def separated_formulas_to_ab(separated_formulas):
    to_ab = ['|']
    for separated_formula in separated_formulas:
        to_ab.append(separated_formula_to_ab(separated_formula))
    return to_ab

def separated_formula_to_ab(separated_formula):
    literals_sys = separated_formula['Y']
    literals_env = separated_formula['X']
    futures = separated_formula['Futures']
    separated_formula_ab = ['&', 'True', 'True']
    for literal in literals_env:
        separated_formula_ab.append(simple_formula_ab(literal))
    for literal in literals_sys:
        separated_formula_ab.append(simple_formula_ab(literal))
    neg_futures = ['|', 'False', 'False']
    for future in futures:
        neg_future_i = ['&', 'True', 'True']
        for f in future:
            neg_future_i.append(simple_formula_ab(f))
        neg_futures.append(neg_future_i)
    separated_formula_ab.append(neg_futures)
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
        
    return res

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



s = empty_separated_formula()