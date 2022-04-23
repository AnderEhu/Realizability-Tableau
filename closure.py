

from temporal_formula import is_always, is_binary, is_eventually, neg_formula_ab, to_str



def calculate_closure(formula):

    if is_binary(formula):
        f_neg = neg_formula_ab(formula)
        f_neg_str = to_str(f_neg)
        f_str = to_str(formula)
        c = {f_neg_str: f_str, f_str: f_neg_str}
        cl = calculate_closure(formula[1])
        cr = calculate_closure(formula[2])
        c.update(cl)
        c.update(cr)
        return c

    elif is_always(formula[0]) or is_eventually(formula[0]):
        neg_formula = neg_formula_ab(formula)
        neg_formula_not_change =  neg_formula_ab(formula, False)
        neg_formula_str = to_str(neg_formula)
        formula_str = to_str(formula)
        c = calculate_closure(formula[1])
        c.update({neg_formula_str: formula_str, formula_str: neg_formula_str, neg_formula_not_change: formula_str, formula_str: neg_formula_not_change})
        return c

    else:
        neg_formula = neg_formula_ab(formula)
        neg_formula_str = to_str(neg_formula)
        formula_str = to_str(formula)
        c =  {neg_formula_str: formula_str, formula_str: neg_formula_str}
        return c
