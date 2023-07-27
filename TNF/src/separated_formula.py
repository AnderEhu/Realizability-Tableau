from TemporalFormula.src.temporal_formula import AND_OPERATORS, AUX_NODE, NEG_AUX_NODE, OR_OPERATOR, OR_OPERATORS, TemporalFormula
from tools import analysis



class SeparatedFormula:

    def __init__(self):
        pass

    @staticmethod
    @analysis
    def empty_separated_formula(**kwargs):
        """
        SeparatedFormula  is represented as a dictionary as follows:
        
        {
            'X': set that represents the conjunction of environment variables
            'Y': set that represents the conjunction of system variables
            'Futures': list of sets represents the disjuction of conjunction of strict future formulas
        }
        """
        sf = dict()
        sf['X'] = set()
        sf['Y'] = set()
        sf['Futures'] = list()
        return sf

    @staticmethod
    @analysis
    def set_separated_formula(X, Y, F, **kwargs):
        """
        Given X, Y, F returns a separated formula 
        Args:
            - X: set that represents the conjunction of environment variables
            - Y: set that represents the conjunction of system variables
            - F:  list of sets represents the disjuction of conjunction of strict future formulas

        Returns:
            returns dictionary representing a separated formula 

        Example:
            Given 
                X: {p_e, r_e}
                Y: {s, c, t}
                F: [{Xa, Xc, Xt}, {-Xa, Xc, -Xt}]
            returns
                {
                    'X': {p_e, r_e}
                    'Y': {s, c, t}
                    'Futures': [{Xa, Xc, Xt}, {-Xa, Xc, -Xt}]
                }

        """
        sf = dict()
        sf['X'] = X
        sf['Y'] = Y
        sf['Futures'] = F
        return sf 

    @staticmethod
    @analysis
    def are_equal_separated_formulas(sf1, sf2, env_minimal_covering = list(), is_sf2_tnf = True, **kwargs):
        """
        Given two separated formulas, sf1 and sf2, returns if sf1 is equivalent to sf2.
        As sf1 and sf2 must satisfy same models, sf1 <--> sf2, i.e. -(sf1 <--> sf2) must be unsat.
        Moreover, 
            sf1 -> sf2 = -sf1 | sf2, so (sf1 & -sf2) must be unsat 
            sf2 -> sf1 = -sf2 | sf1, so (sf2 & -sf1) must be unsat 
            
        Args:
            - sf1: a separated formula
            - sf2: a separated formula
            - env_minimal_covering: list of possible environment valuations
            - is_sf2_tnf: if sf2 represent a tnf, system literals are not included.
        Returns:
            True, if sf1 is equivalent to sf2, otherwise, False 
        """
        if sf1 == sf2:
            return True

        if env_minimal_covering:
            neg_minimal_covering = TemporalFormula.neg_formula_ab(env_minimal_covering)
        else:
            env_minimal_covering = ['|', AUX_NODE, ["-", AUX_NODE]]
            neg_minimal_covering = ['&', AUX_NODE, ["-", AUX_NODE]]


        neg_sf1_ab = ['|', SeparatedFormula.neg_separated_formulas_to_ab(sf1, is_sf2_tnf, **kwargs), neg_minimal_covering]
        neg_sf2_ab = ['|', SeparatedFormula.neg_separated_formulas_to_ab(sf2, is_sf2_tnf, **kwargs), neg_minimal_covering]
        
        

        sf1_ab = ['&', SeparatedFormula.separated_formulas_to_ab(sf1, is_sf2_tnf, **kwargs), env_minimal_covering]

        sf2_ab = ['&', SeparatedFormula.separated_formulas_to_ab(sf2, is_sf2_tnf, **kwargs), env_minimal_covering]

        

        f1toAB = ['&', sf2_ab, neg_sf1_ab]
        f2toAB = ['&', sf1_ab, neg_sf2_ab]

        f = ['|', f1toAB, f2toAB]
        if TemporalFormula.is_sat(f, **kwargs):
            return False
        else:
            return True
       
        

        # if TemporalFormula.is_sat(f1toAB, **kwargs):
        #     return False
        # elif TemporalFormula.is_sat(f2toAB, **kwargs):
        #     return False
        # else:
        #     return True



    @staticmethod
    @analysis
    def neg_separated_formulas_to_ab(separated_formulas, is_tnf, **kwargs):
        """
            Return the negation of the given disjunction separated formulas as list of lists, if is_tnf equals to True, system variables are not included
            
            Example,
                separated_formulas = [sf1, sf2, sf3, sf4] == sf1 | sf2 | sf3 | sf4, so the negation as list of lists is equal to 
                ['&', neg_separated_formula_to_ab(sf1), neg_separated_formula_to_ab(sf2), neg_separated_formula_to_ab(sf3), neg_separated_formula_to_ab(sf4)]

        """
        to_ab = ['&']
        for separated_formula in separated_formulas:
            separated_formula_ab = SeparatedFormula.neg_separated_formula_to_ab(separated_formula, is_tnf, **kwargs)
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
    def neg_separated_formula_to_ab(separated_formula, is_tnf, **kwargs):
        """
            Return the negation of the given separated formula as list of lists, if is_tnf equals to True, system variables are not included.
            Negation is as follows:
                Given a separated_formula = {
                    X: {p_e, r_e}
                    Y: {s, c, t}
                    F: [{Xa, Xc, Xt}, {-Xa, Xc, -Xt}
                } 

                can we see {} as conjunction and [] as disjuction of formulas, so:

                separated_formula = ['&',['&','p_e', 'r_e'], ['&', 's', 'c', 't'], ['|', ['&', 'Xa', 'Xc', 'Xt'], ['&', ['-', 'Xa'], 'Xc', ['-', 'Xt']]]] and
                negation of separated_formula = ['-', ['&',['&','p_e', 'r_e'], ['&', 's', 'c', 't'], ['|', ['&', 'Xa', 'Xc', 'Xt'], ['&', ['-', 'Xa'], 'Xc', ['-', 'Xt']]]]] we distribute the negation and
                negation of separated_formula distributed = ['|',['|',['-', 'p_e'], ['-', 'r_e']], ['|', ['-', 's'], ['-', 'c'], ['-', 't']], ['&', ['&', ['-','Xa'], ['-','Xc'], ['-','Xt']], ['|', 'Xa', ['-','Xc'], 'Xt']]]



        """

        literals_env = separated_formula['X']
        futures = separated_formula['Futures']


        neg_separated_formula_ab = ['|']
        if not literals_env:
            neg_separated_formula_ab.append(TemporalFormula.simple_negation_ab('True', **kwargs))
        for literal in literals_env:
            neg_separated_formula_ab.append(TemporalFormula.simple_negation_ab(literal, **kwargs))
        
        if not is_tnf:
            literals_sys = separated_formula['Y']
            if not literals_sys:
                neg_separated_formula_ab.append(TemporalFormula.simple_negation_ab('True', **kwargs))
            for literal in literals_sys:
                neg_separated_formula_ab.append(TemporalFormula.simple_negation_ab(literal))

        futures_ab = ['&']
        if not futures:
            futures_ab.append('X[1]True')
        for future in futures:
            futures_i_ab = ['|']
            if not future:
                futures_i_ab.append('X[1]False')
            for f in future:
                futures_i_ab.append(TemporalFormula.simple_negation_ab(f, **kwargs))
        
            futures_i_ab = TemporalFormula.fix_ab_list(futures_i_ab, **kwargs)
            if futures_i_ab:  
                futures_ab.append(futures_i_ab)
        
        futures_ab = TemporalFormula.fix_ab_list(futures_ab, **kwargs)
        
        if futures_ab:
            neg_separated_formula_ab.append(futures_ab)
        
        neg_separated_formula_ab = TemporalFormula.fix_ab_list(neg_separated_formula_ab, **kwargs)

        
        return neg_separated_formula_ab

    @staticmethod
    @analysis
    def print_separated_formula(separated_formula, AND = " ∧ ", OR = " v ", **kwargs):
        """
        Given a separated formula it returns equivalent temporal formula as string, for example,
        {X: {p_e, r_e}, Y: {s, c, t}, F: [{Xa, Xc, Xt}, {-Xa, Xc, -Xt}] returns 
            
        """
        res = ""
        for fi in separated_formula:
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

    @staticmethod
    @analysis
    def dnf_to_sf(dnf,  **kwargs):
        """
        Given a dnf as lists of sets, it returns the equivalent disjunction of separated formula, for example,
        if dnf = [{p_e, r_e, s, c, t, Xa, Xc, Xt}, {p_e, r_e, -s, -c, t, -Xa, Xc, -Xt} ] 
        
        returns [{
                    'X': {p_e, r_e}
                    'Y': {s, c, t}
                    'F': [{Xa, Xc, Xt}]
                },{
                    'X': {p_e, r_e}
                    'Y': {-s, -c, t}
                    'Futures' [{-Xa, Xc, -Xt}]
                }]
        
        
        """   
        sfs = []
        for model in dnf:
            to_sf = SeparatedFormula.model_to_separated_formula(model, **kwargs)
            sfs.append(to_sf)
        return sfs

    @staticmethod
    @analysis
    def model_to_separated_formula(model,  **kwargs):
        """
        Given a model as a sets, it returns the equivalent separated formula, for example,
        
        dnf = {p_e, r_e, s, c, t, Xa, Xc, Xt} returns {'X': {p_e, r_e}, 'Y': {s, c, t}, 'F': [{Xa, Xc, Xt}]}
        
        
        """
        sf = SeparatedFormula.empty_separated_formula(**kwargs)
        
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
    def separated_formulas_to_ab(separated_formulas, is_tnf, **kwargs):
        """

        Return the given separated formulas as list of lists, if is_tnf equals to True, system variables are not included
        
        """
        to_ab = ['|']
        for separated_formula in separated_formulas:
            separated_formula_ab = SeparatedFormula.separated_formula_to_ab(separated_formula, is_tnf, **kwargs)
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
    def separated_formula_to_ab(separated_formula, is_tnf, **kwargs):
        """
            Return  given separated formula as list of lists, if is_tnf equals to True, system variables are not included.
                Given a separated_formula = {
                    X: {p_e, r_e}
                    Y: {s, c, t}
                    F: [{Xa, Xc, Xt}, {-Xa, Xc, -Xt}
                } 

                can we see {} as conjunction and [] as disjuction of formulas, so:

                separated_formula = ['&',['&','p_e', 'r_e'], ['&', 's', 'c', 't'], ['|', ['&', 'Xa', 'Xc', 'Xt'], ['&', ['-', 'Xa'], 'Xc', ['-', 'Xt']]]] 


        """
        literals_env = separated_formula['X']
        futures = separated_formula['Futures']

        separated_formula_ab = ['&']
        
        if not literals_env:
            separated_formula_ab.append(TemporalFormula.simple_formula_ab('True', **kwargs))
        for literal in literals_env:
            separated_formula_ab.append(TemporalFormula.simple_formula_ab(literal, **kwargs))
        
        if not is_tnf:
            literals_sys = separated_formula['Y']
            if not literals_sys:
                separated_formula_ab.append(TemporalFormula.simple_formula_ab('True', **kwargs))
            for literal in literals_sys:
                separated_formula_ab.append(TemporalFormula.simple_formula_ab(literal))

        futures_ab = ['|']
        if not futures:
            futures_ab.append('X[1]False')
        for future in futures:
            futures_i_ab = ['&']
            if not future:
                futures_i_ab.append('X[1]True')
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
    def separated_formula_strict_futures_to_ab(strict_future_formulas):
        strict_future_next_formulas = [OR_OPERATORS]
        for or_strict_formula in strict_future_formulas:
            and_strict_next_formulas = [AND_OPERATORS]
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



    @staticmethod
    def get_separated_formula_compatibles_by_env(env_move, separated_formulas):
        """
        Given a env_move and separated formulas, it returns the separated formulas compatibles with env_move

        Args:
            - env_move: set of environment variables 
            - separated_formula: a separated formula

        Return:
            Separated formulas compatible with given environment variables valuation.

        """
        compatibles = list()
        for sf in separated_formulas:
            env_sf = sf['X']
            if SeparatedFormula.is_consistent(env_sf, env_move):
                compatibles.append(sf)
        return compatibles

    
    @staticmethod
    def is_consistent(set_literals_1, set_literals_2, **kwargs):
        """
        Given two set of literals, set_literals_1 and set_literals_2, it returns if the conjunction of both is consistent
        
        Args:
            - set_literals_1: set of literals 
            - set_literals_2:  set of literals 
        
        Return:
            True, if they are consisten, otherwise, False

        Example:
            if set_literals_1 = {'p_e', 's'} and  set_literals_2 = {'r_e', 's'} then it retuns True (consistent {'p_e', 'r_e', 's'}),
            whereas,  if set_literals_1 = {'p_e', 's'} and  set_literals_2 = {'r_e', '-s'} then it returns False (inconsistent s and -s)

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






