
from covering import get_env_minimal_covering
from temporal_formula import TemporalFormula, calculate_dnf, get_all_assignments, neg_literal
from tnf import TNF


class Tableau:
    def __init__(self, initial_formula_str, safety_formula_str, env_constraints_str):
        print(initial_formula_str, safety_formula_str, env_constraints_str)
        self.init = TemporalFormula(initial_formula_str)
        self.safety_formula = TemporalFormula(safety_formula_str)
        self.env_constraints = TemporalFormula(env_constraints_str)
        self.ab = ['&', self.init.ab, self.safety_formula.ab, self.env_constraints.ab]
        env_vars = self.safety_formula.env_vars
        all_assignments = get_all_assignments(env_vars)
        valid_assignments = calculate_dnf(self.env_constraints.ab)
        self.env_minimal_covering = get_env_minimal_covering(all_assignments, valid_assignments)
        
        self.safety_formula_TNF = TNF(self.ab, env_vars, self.env_minimal_covering)




