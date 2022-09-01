

from TemporalFormula.src.temporal_formula import AND_OPERATOR, AUX_NODE, NEG_OPERATOR, OR_OPERATOR, TemporalFormula
from tools import analysis


class TableauRules:
    @staticmethod
    @analysis
    def next(formulaStr, strToAb, **kwargs):
        if formulaStr == 'X[1]True':
            return ['|', 'aux_var', ['-', 'aux_var']]
        formulaAb = TemporalFormula.get_str_to_ab_in_bica(formulaStr, strToAb, **kwargs) 
        #print(formulaStr, "===>", formulaAb)
        if TemporalFormula.is_neg(formulaAb[0], **kwargs):
            return TableauRules.apply_next_rule_to_negative_formula(formulaAb[1], strToAb, **kwargs)
        else:
            return TableauRules.apply_next_rule_to_positive_formula(formulaAb, strToAb, **kwargs)

    @staticmethod
    @analysis
    def apply_next_rule_to_positive_formula(formulaAb, strToAb, **kwargs):
        if TemporalFormula.is_next(formulaAb[0], **kwargs):
            return TableauRules.apply_next_rule_to_next_positive_formula(formulaAb, strToAb, **kwargs)
        else:
            assert TemporalFormula.is_always(formulaAb[0], **kwargs) or TemporalFormula.is_eventually(formulaAb[0], **kwargs)
            return TableauRules.apply_next_rule_to_eventually_or_always_positive_formula(formulaAb, strToAb, **kwargs)
        

    @staticmethod
    @analysis
    def apply_next_rule_to_next_positive_formula(formulaAb, strToAb, **kwargs):
        number_of_nexts = TemporalFormula.get_next_n(formulaAb[0], **kwargs)

        if number_of_nexts > 1:
            next_rule_applied_to_formula_ab =  [TemporalFormula.set_next_n(number_of_nexts-1, **kwargs), formulaAb[1]]
        else: 
            if isinstance(formulaAb[1], str):
                next_rule_applied_to_formula_ab =  formulaAb[1]
            else:
                next_rule_applied_to_formula_ab =  TemporalFormula.split_future_formula(formulaAb[1], **kwargs)

        #print(formulaAb, "  NEXT ", next_rule_applied_to_formula_ab)
        
        return next_rule_applied_to_formula_ab

    @staticmethod
    @analysis
    def apply_next_rule_to_eventually_or_always_positive_formula(formulaAb, strToAb, **kwargs):
        limitInf, limitSup = TemporalFormula.get_eventually_always_op_limits(formulaAb[0])
        new_limitInf, new_limitSup = limitInf - 1, limitSup - 1
        if new_limitInf > 0:
            if TemporalFormula.is_always(formulaAb[0]):
                return [TemporalFormula.set_always_interval(new_limitInf, new_limitSup, **kwargs), formulaAb[1]]
            else:
                return [TemporalFormula.set_eventually_interval(new_limitInf, new_limitSup, **kwargs), formulaAb[1]]
        else:
            if new_limitInf + 1 == new_limitSup:
                if TemporalFormula.is_always(formulaAb[0]):
                    return [AND_OPERATOR, formulaAb[1],[TemporalFormula.set_next_n(new_limitSup, **kwargs), formulaAb[1]]]
                else:
                    return [OR_OPERATOR, formulaAb[1], [TemporalFormula.set_next_n(new_limitSup, **kwargs), formulaAb[1]]]
            else:
                if TemporalFormula.is_always(formulaAb[0]):
                    return [AND_OPERATOR, formulaAb[1], [TemporalFormula.set_always_interval(new_limitInf+1, new_limitSup,  **kwargs), formulaAb[1]]]
                else:
                    return [OR_OPERATOR, formulaAb[1], [TemporalFormula.set_eventually_interval(new_limitInf+1, new_limitSup, **kwargs), formulaAb[1]]]
    
            
    @staticmethod
    @analysis
    def apply_next_rule_to_negative_formula(formulaAb, strToAb, **kwargs):
        return [NEG_OPERATOR, TableauRules.apply_next_rule_to_positive_formula(formulaAb, strToAb, **kwargs)]

    @staticmethod
    @analysis
    def apply_next_rule_to_list_strict_formulas_sets(strict_future_formulas, strToAb, **kwargs):

        strict_future_next_formulas = [OR_OPERATOR]
        for or_strict_formula in strict_future_formulas:
            and_strict_next_formulas = [AND_OPERATOR]
            for and_strict_formula in or_strict_formula:
                and_next_strict_formula = TableauRules.next(and_strict_formula, strToAb, **kwargs)
                and_strict_next_formulas.append(and_next_strict_formula)

            if len(and_strict_next_formulas) == 2:
                and_strict_next_formulas = and_strict_next_formulas[1]
            #print("\n", or_strict_formula, "NEXT ==> \n", and_strict_next_formulas)
            strict_future_next_formulas.append(and_strict_next_formulas)
        if len(strict_future_next_formulas) == 2:
            strict_future_next_formulas_next_rule_applied =  strict_future_next_formulas[1]

        elif len(strict_future_next_formulas) > 2:
            strict_future_next_formulas_next_rule_applied =  strict_future_next_formulas
        else:
            strict_future_next_formulas_next_rule_applied =  [OR_OPERATOR, AUX_NODE, ['-', AUX_NODE]]

        return strict_future_next_formulas_next_rule_applied
