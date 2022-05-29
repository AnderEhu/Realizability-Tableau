
from temporal_formula import AND_OPERATOR, AUX_NODE, NEG_OPERATOR, OR_OPERATOR, TemporalFormula
from tnf import TNF
from tools import analysis

ENVIRONMENT_PLAYING = 0
SYSTEM_PLAYING = 1

class TableauNode:
    def __init__(self, formula, previous_node, **kwargs):
        self.formula = formula
        self.previous_node = previous_node

    @analysis
    def is_success_node(self, **kwargs):
        return self.is_implicated_by_a_previous_node(self.previous_node, **kwargs)

    @analysis
    def is_implicated_by_a_previous_node(self, prev_node, **kwargs):
        if not prev_node:
            return False
        else:
            is_actual_node_implicated = TemporalFormula.is_implicated(prev_node.formula, self.formula, **kwargs)
            if is_actual_node_implicated:
                print(prev_node.formula, "IMPLIES", self.formula)
                return True
            else:
                print(prev_node.formula, "NOT IMPLIES", self.formula)
                return self.is_implicated_by_a_previous_node(prev_node.previous_node, **kwargs)

class TableauRules:
    @staticmethod
    @analysis
    def next(formulaStr, strToAb, **kwargs):
        formulaAb = TemporalFormula.getStrToAb(formulaStr, strToAb, **kwargs) 
        if TemporalFormula.is_neg(formulaStr[0], **kwargs):
            return TableauRules.apply_next_rule_to_negative_formula(formulaAb[1], strToAb, **kwargs)
        else:
            return TableauRules.apply_next_rule_to_positive_formula(formulaAb, strToAb, **kwargs)

    @staticmethod
    @analysis
    def apply_next_rule_to_positive_formula(formulaAb, strToAb, **kwargs):


        assert TemporalFormula.is_next(formulaAb[0], **kwargs)

        number_of_nexts = TemporalFormula.get_next_n(formulaAb[0], **kwargs)

        assert number_of_nexts > 0

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
    def apply_next_rule_to_negative_formula(formulaAb, strToAb, **kwargs):
        return [NEG_OPERATOR, TableauRules.apply_next_rule_to_positive_formula(formulaAb, strToAb, **kwargs)]

    @staticmethod
    @analysis
    def apply_next_rule_to_strict_formulas(strict_future_formulas, strToAb, **kwargs):

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



class Tableau:
    def __init__(self, initial_formula_str, safety_formula_str, env_constraints_str, **kwargs):
        self.strToAb = dict()
        
        self.safety_formula = TemporalFormula(safety_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = True,  activate_type_of_variables = True, activate_subsumptions = False, activate_strToAb = True, **kwargs)
        self.env_constraints = TemporalFormula(env_constraints_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = True,  activate_type_of_variables = True, activate_subsumptions = False, activate_strToAb = True, **kwargs)
        self.initial_formula = TemporalFormula(initial_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = True,  activate_type_of_variables = True, activate_subsumptions = False, activate_strToAb = True, **kwargs)
        
        #self.subsumption = calculate_subsumptions(self.init.type_of_variables, self.safety_formula.type_of_variables)
        self.strToAb.update(self.safety_formula.strToAb)
        self.strToAb.update(self.env_constraints.strToAb)

        self.env_vars = self.safety_formula.env_vars
        all_assignments = TemporalFormula.get_all_assignments(self.env_vars, **kwargs)
        valid_assignments = TemporalFormula.calculate_dnf(self.env_constraints.ab, **kwargs)
        self.env_minimal_covering = Tableau.get_env_minimal_covering(all_assignments, valid_assignments, **kwargs)

        self.initial_node = TableauNode(self.initial_formula.ab, None)

        print(self.tableau(self.initial_node, ENVIRONMENT_PLAYING, 0, **kwargs))




    def __print_dict(self, d):
        for key, value in d.items():
            print(key, ": ", value, "\n")

        
    @analysis
    def tableau(self, node, player, depth, **kwargs):
        
        if self.is_environment_playing(player, **kwargs):
            print("ENVIRONMENT PLAYING")
            if node.is_success_node(**kwargs):
                return True

            node_tnf = self.calculate_tnf_with_node(node.formula, **kwargs)

            if node_tnf.is_not_X_covering(**kwargs):
                return False
            else:
                all_minimal_X_coverings = node_tnf.get_all_minimal_X_coverings(**kwargs)
                i_minimal_X_covering = 1
                for minimal_X_covering in all_minimal_X_coverings:
                    is_open = False
                    i_env_assignment = 1
                    for env_assignment, child in minimal_X_covering.items():
                        formula = [AND_OPERATOR, env_assignment, child[0], child[1]]
                        child_node = TableauNode(formula, node)   
                        is_open = self.tableau(child_node, SYSTEM_PLAYING, depth, **kwargs)
                        print("IS_OPEN?",is_open, "For ", env_assignment, i_minimal_X_covering, " / ", len(all_minimal_X_coverings), " minimal X covering and ", i_env_assignment, " / ", len(self.env_minimal_covering), "environment assignment",  "Depth: ", depth)
                        i_env_assignment+=1
                        if not is_open:
                            break
                    if is_open:
                        return True
                    i_minimal_X_covering += 1
                return False
    
        else:
            print("SYS PLAYING")
            env_assignment = node.formula[1]
            sys_assignments = node.formula[2]
            strict_future_formulas = node.formula[3]
            next_formula = TableauRules.apply_next_rule_to_strict_formulas(strict_future_formulas, self.strToAb, **kwargs)
            child_node = TableauNode(next_formula, node.previous_node)
            is_open = self.tableau(child_node, ENVIRONMENT_PLAYING, depth+1, **kwargs)

            
        return is_open




    @analysis
    def calculate_tnf_with_node(self, node, **kwargs):

        nodeTnf = TNF(['&', self.safety_formula.ab, self.env_constraints.ab, node], self.env_vars, self.env_minimal_covering, **kwargs)
        
        return nodeTnf


    @analysis
    def is_environment_playing(self, player, **kwargs):
        return player == ENVIRONMENT_PLAYING

    @analysis    
    def empty_tableau_node(self, **kwargs):
        node = dict()
        node['System'] = set()
        node['Environment'] = set()
        node['Strict Future'] = set()
        return node

    
    @staticmethod
    @analysis
    def get_env_minimal_covering(all_assignments, valid_assignments, **kwargs):
        if not valid_assignments:
            return all_assignments
        env_minimal_covering = list()
        for assignment in all_assignments:
            if Tableau.is_valid_assignment(assignment, valid_assignments, **kwargs):
                env_minimal_covering.append(assignment)
        return env_minimal_covering

    @staticmethod
    @analysis
    def is_valid_assignment(assignment, valid_assignments, **kwargs):
        for valid_assignment in valid_assignments:
            valid = True
            neg_literals_valid_assignment = [ TemporalFormula.neg_literal(env_literal, **kwargs) for env_literal in assignment]
            for neg_literal_valid_assignment in neg_literals_valid_assignment:
                if neg_literal_valid_assignment in valid_assignment:
                    valid = False
                    break
            if not valid:
                continue
            else:
                return True
        return False


