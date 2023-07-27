
from TNF.src.inconsistencies import Inconsistencies
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
        self.different_node_env_valid_evaluations = dict()
        self.success_nodes = set()
        self.failed_nodes = set()
        self.success_back_to_higher_deep = None
        self.failed_back_to_higher_deep = None

        self.inconsistencies = dict()
        
        self.safety_formula = TemporalFormula(safety_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)
        self.env_constraints = TemporalFormula(env_constraints_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)
        self.initial_formula = TemporalFormula(initial_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)

        self.environment_safety_formula_variables = TemporalFormula.get_environment_current_variables(self.safety_formula.ab)
        self.valid_assignments = TemporalFormula.calculate_dnf(self.env_constraints.ab, **kwargs)
        self.initial_node = TableauNode(self.initial_formula.ab, 1, None)


        self.is_open = self.tableau(self.initial_node, ENVIRONMENT_PLAYING, 1, **kwargs)

        print(self.inconsistencies)
        print(self.strToAb)



        
    @analysis
    def tableau(self, node: TableauNode, player: int, depth: int, **kwargs):
        
        if self.is_environment_playing(player, **kwargs):
            print("ENVIRONMENT PLAYING", "Depth: ", depth)

            node_formula_str = TemporalFormula.to_str(node.formula)
            self.strToAb[node_formula_str] = node.formula

            if node.implicate_a_failure_nodes(self.failed_nodes, self.strToAb):
                print("IMPLICATE A FAILED NODE")
                return False

            if node.is_implicated_by_success_nodes(self.success_nodes, self.strToAb):
                print("IMPLICATED BY A SUCCESS NODE")
                return True
            if node.has_open_branch(**kwargs):
                print("OPEN BRANCH")
                return True
                
            env_vars_node = frozenset(self.environment_safety_formula_variables.union(TemporalFormula.get_environment_current_variables(node.formula)))

            node_tnf = self.calculate_tnf_with_node(node.formula, env_vars_node, **kwargs)

            TNF.print_tnf(node_tnf)
            
            if MinimalCovering.is_not_X_covering(node_tnf):
                print("NO MINIMAL COVERING, NODE CLOSED")
                return False
            else:
                env_valuations_sorted, minimal_X_coverings_iterator = MinimalCovering.sort_minimal_coverings(node_tnf)
                
                for minimal_X_covering in minimal_X_coverings_iterator:
                    i_env_assignment = 1
                    minimal_X_covering = list(minimal_X_covering)
                    minimal_X_covering.reverse()
                    env_valuations_sorted.reverse()
                    is_open = False
                    for i, child in enumerate(minimal_X_covering):

                        env_assignment = env_valuations_sorted[i]
                        strict_futures_i = Inconsistencies.delete_inconsistent_sets(child[1], self.inconsistencies, self.strToAb)
                        if not strict_futures_i: break

                        #formula = [AND_OPERATOR, env_assignment, child[0], strict_futures_i]
                        
                        child_node = TableauNode(strict_futures_i, depth, node)

                        is_open = self.tableau(child_node, SYSTEM_PLAYING, depth, **kwargs)

                        if is_open is False:
                            print("IS CLOSED For ", env_assignment,  i_env_assignment, " / ", len(env_valuations_sorted), "environment assignment",  "Depth: ", depth)
                            break
                        elif is_open is True:
                            print("IS OPEN For ", env_assignment,  i_env_assignment, " / ", len(env_valuations_sorted), "environment assignment",  "Depth: ", depth)
                            i_env_assignment+=1
                        elif depth == int(abs(is_open)) and is_open > 0:
                            print("A LOWER TABLEAU NODE OPEN THIS NODE")
                            return True

                        elif depth == int(abs(is_open)) and is_open < 0:
                            print("A LOWER TABLEAU NODE CLOSED THIS NODE")
                            return False

                        elif depth != int(abs(is_open)):
                            if is_open > 0:
                                print("A HIGHER TABLEAU NODE HAS BEEN OPEN ==> GOIND BACK TO NODE AT DEPTH", is_open)
                            if is_open < 0:
                                print("A HIGHER TABLEAU NODE HAS BEEN CLOSED ==> GOIND BACK TO NODE AT DEPTH", is_open)
                            return is_open
                        else:
                            assert False


                    if is_open:
                        print("SUCCESS NODE ADDED", is_open)
                        self.success_nodes.add(node_formula_str)
                        print("LOOKING FOR PREVIOUS WEAKER NODE TO CLOSE IT")
                        is_success_previous_node = node.success_previous_node(node_formula_str, self.strToAb)
                        if is_success_previous_node:
                            print("GOING BACK TO NODE AT DEPTH ", is_success_previous_node, " TO OPEN IT" )
                            return float(is_success_previous_node)
                        else:
                            print("NO PREVIOUS WEAKER NODE DETECTED")
                            return True
                    else:
                        print("MINIMAL COVERING FAILED")
                        try:
                            next(minimal_X_coverings_iterator)
                            print("CHANGING TO ANOTHER MINIMAL COVERING")
                        except StopIteration:
                            print("NO MINIMAL COVERING: FAILED NODE")
                            self.failed_nodes.add(node_formula_str)
                            print("LOOKING FOR PREVIOUS STRONGER NODE TO CLOSE IT")
                            is_failed_previous_node = node.failed_previous_node(node_formula_str, self.strToAb)
                            if is_failed_previous_node:
                                print("GOING BACK TO NODE AT DEPTH ", is_failed_previous_node, " TO CLOSE IT" )
                                return float(is_failed_previous_node * -1)
                            else:
                                print("NO PREVIOUS STRONGER NODE DETECTED")
                                return False
            return False




    
        else:
            print("SYSTEM PLAYING", "Depth: ", depth)
            #list_strict_future_sets = node.formula[3]
            print("\nFUTURE FORMULAS BEFORE NEXT: \n", node.formula)
            formula_after_next = TableauRules.apply_next_rule_to_list_strict_formulas_sets(node.formula, self.strToAb, **kwargs)
            print("\FUTURE FORMULAS AFTER NEXT: \n", formula_after_next)
            child_node = TableauNode(formula_after_next, depth+1, node.previous_node)
            is_open = self.tableau(child_node, ENVIRONMENT_PLAYING, depth+1, **kwargs)

            return is_open




    @analysis
    def calculate_tnf_with_node(self, node, env_vars_node, **kwargs):

        
        if frozenset(env_vars_node) in self.different_node_env_valid_evaluations:
            env_valid_valuations = self.different_node_env_valid_evaluations[frozenset(env_vars_node)]
        else:
            all_env_assignments = TemporalFormula.get_all_assignments(env_vars_node, **kwargs)
            env_valid_valuations = TemporalFormula.get_valid_env_valuations(all_env_assignments, self.valid_assignments)
            self.different_node_env_valid_evaluations[frozenset(env_vars_node)] = env_valid_valuations

        temporal_formula = ['&', self.safety_formula.ab, self.env_constraints.ab, node]

        node_tnf = TNF(temporal_formula=temporal_formula, env_vars=env_vars_node,valid_env_valuations=env_valid_valuations,  env_constraints_ab=self.env_constraints.ab, inconsistencies = self.inconsistencies, **kwargs)
        
        return node_tnf.tnf_formula


    @analysis
    def is_environment_playing(self, player, **kwargs):
        return player == ENVIRONMENT_PLAYING


