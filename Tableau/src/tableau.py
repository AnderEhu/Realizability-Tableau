
from numpy import Inf
from Tableau.src.minimal_covering import MinimalCovering
from Tableau.src.tableau_node import TableauNode
from Tableau.src.tableau_rules import TableauRules
from TemporalFormula.src.temporal_formula import AND_OPERATOR, AUX_NODE, NEG_OPERATOR, OR_OPERATOR, TemporalFormula
from TNF.src.tnf import TNF
from tools import analysis

ENVIRONMENT_PLAYING = 0
SYSTEM_PLAYING = 1



class Tableau:
    def __init__(self, initial_formula_str, safety_formula_str, env_constraints_str, **kwargs):
        self.strToAb = dict()
        
        self.safety_formula = TemporalFormula(safety_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)
        self.env_constraints = TemporalFormula(env_constraints_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)
        self.initial_formula = TemporalFormula(initial_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)

        self.env_vars_safety_formula = TemporalFormula.get_env_actual_variables(self.safety_formula.ab)
        self.valid_assignments = TemporalFormula.calculate_dnf(self.env_constraints.ab, **kwargs)
        self.initial_node = TableauNode(self.initial_formula.ab, 0, None)
        self.env_minimal_coverings = dict()
        self.success_nodes = set()
        self.failed_nodes = set()
        self.success_back_to_higher_deep = None
        self.failed_back_to_higher_deep = None


        print(self.tableau(self.initial_node, ENVIRONMENT_PLAYING, 0, **kwargs))




    def __print_dict(self, d):
        for key, value in d.items():
            print(key, ": ", value, "\n")

        
    @analysis
    def tableau(self, node, player, depth, **kwargs):
        
        if self.is_environment_playing(player, **kwargs):
            print("ENVIRONMENT PLAYING", "Depth: ", depth)

            node_formula_str = TemporalFormula.to_str(node.formula)


            self.strToAb[node_formula_str] = node.formula

            if node.implicate_a_failure_nodes(self.failed_nodes, self.strToAb):
                print("IMPLICATED A FAILED NODE")
                return False

            if node.is_implicated_by_success_nodes(self.success_nodes, self.strToAb):
                print("IMPLICATED BY A SUCCESS NODE")
                return True
            
            if node.has_open_branch(**kwargs):
                print("OPEN BRANCH")
                return True

            node_tnf = self.calculate_tnf_with_node(node.formula, **kwargs)
            
            if MinimalCovering.is_not_X_covering(node_tnf):
                return False
            else:
                all_minimal_X_coverings = MinimalCovering.get_all_minimal_X_coverings_sorted(node_tnf, self.env_minimal_coverings)
                i_minimal_X_covering = 1
                for minimal_X_covering in all_minimal_X_coverings:
                    i_env_assignment = 1
                    for env_assignment, child in minimal_X_covering.items():
                        formula = [AND_OPERATOR, env_assignment, child[0], child[1]]
                        child_node = TableauNode(formula, depth + 1, node)   
                        is_open = self.tableau(child_node, SYSTEM_PLAYING, depth, **kwargs)
                        if is_open is False:
                            break
                        elif is_open is True:
                            print("IS_OPEN?",is_open, "For ", env_assignment, i_minimal_X_covering, " / ", len(all_minimal_X_coverings), " minimal X covering and ", i_env_assignment, " / ", len(minimal_X_covering.keys()), "environment assignment",  "Depth: ", depth)
                            i_env_assignment+=1
                        else:
                            print(is_open, type(is_open))
                            assert isinstance(is_open, float)
                            if depth == int(abs(is_open)):
                                if is_open >= 0:
                                    return True
                                else:
                                    return False
                            else:
                                return is_open

                    if is_open:
                        print("SUCCESS NODE ADDED", is_open)
                        self.success_nodes.add(node_formula_str)
                        is_success_previous_node = node.success_previous_node(node_formula_str, self.strToAb)
                        if is_success_previous_node:
                            return float(is_success_previous_node)
                        else:
                            return True
                    i_minimal_X_covering += 1
                print("FAILED NODE ADDED", is_open)
                self.failed_nodes.add(node_formula_str)
                is_failed_previous_node = node.failed_previous_node(node_formula_str, self.strToAb)
                if is_failed_previous_node:
                    return float(is_failed_previous_node * -1)
                else:
                    return False
    
        else:
            print("SYS PLAYING")
            env_assignment = node.formula[1]
            sys_assignments = node.formula[2]
            strict_future_formulas = node.formula[3]
            if strict_future_formulas == [{'X[1]False'}] or sys_assignments == {'False'}:
                print("FALSE; ", node.formula)
                return False
            next_formula = TableauRules.apply_next_rule_to_strict_formulas(strict_future_formulas, self.strToAb, **kwargs)
            child_node = TableauNode(next_formula, depth+1, node.previous_node)
            is_open = self.tableau(child_node, ENVIRONMENT_PLAYING, depth+1, **kwargs)

            return is_open




    @analysis
    def calculate_tnf_with_node(self, node, **kwargs):


        env_vars_node = self.env_vars_safety_formula.union(TemporalFormula.get_env_actual_variables(node))
        if frozenset(env_vars_node) in self.env_minimal_coverings:
            env_node_minimal_covering = self.env_minimal_coverings[frozenset(env_vars_node)]
        else:
            all_assignments = TemporalFormula.get_all_assignments(env_vars_node, **kwargs)
            env_node_minimal_covering = Tableau.get_env_minimal_covering(all_assignments, self.valid_assignments, **kwargs)
            self.env_minimal_coverings[frozenset(env_vars_node)] = env_node_minimal_covering
        #print(self.safety_formula.ab)
        #print(['&', self.safety_formula.ab, self.env_constraints.ab, node])
        nodeTnf = TNF(['&', self.safety_formula.ab, self.env_constraints.ab, node], env_vars_node, env_node_minimal_covering, **kwargs)
        
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


