
from numpy import Inf
from temporal_formula import AND_OPERATOR, AUX_NODE, NEG_OPERATOR, OR_OPERATOR, TemporalFormula
from tnf import TNF
from tools import analysis

ENVIRONMENT_PLAYING = 0
SYSTEM_PLAYING = 1

class TableauNode:
    def __init__(self, formula, depth, previous_node, **kwargs):
        self.formula = formula
        self.depth = depth
        self.previous_node = previous_node

    @analysis
    def has_open_branch(self, **kwargs):
        return self.is_implicated_by_a_previous_node(self.previous_node, **kwargs)

    @analysis
    def is_implicated_by_a_previous_node(self, prev_node, **kwargs):
        if not prev_node:
            return None
        else:
            is_actual_node_implicated = TemporalFormula.is_implicated(prev_node.formula, self.formula, **kwargs)
            if is_actual_node_implicated:
                #print(prev_node.formula, " IMPLIES ", self.formula)
                return prev_node.depth
            else:
                #print(prev_node.formula, " NOT IMPLIES ", self.formula)
                return self.is_implicated_by_a_previous_node(prev_node.previous_node, **kwargs)

class TableauRules:
    @staticmethod
    @analysis
    def next(formulaStr, strToAb, **kwargs):
        if formulaStr == 'X[1]True':
            return ['|', 'aux_var', ['-', 'aux_var']]
        formulaAb = TemporalFormula.getStrToAb(formulaStr, strToAb, **kwargs) 
        print(formulaStr, "===>", formulaAb)
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
        limitInf, limitSup = TemporalFormula.get_temporal_op_limits(formulaAb[0])
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
        
        self.safety_formula = TemporalFormula(safety_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)
        self.env_constraints = TemporalFormula(env_constraints_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)
        self.initial_formula = TemporalFormula(initial_formula_str, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True, **kwargs)

        self.env_vars_safety_formula = TemporalFormula.get_env_actual_variables(self.safety_formula.ab)
        self.valid_assignments = TemporalFormula.calculate_dnf(self.env_constraints.ab, **kwargs)
        self.initial_node = TableauNode(self.initial_formula.ab, 0, None)
        self.env_minimal_coverings = dict()
        self.success_nodes = list()
        self.failed_nodes = list()

        print(self.tableau(self.initial_node, ENVIRONMENT_PLAYING, 0, **kwargs))




    def __print_dict(self, d):
        for key, value in d.items():
            print(key, ": ", value, "\n")

        
    @analysis
    def tableau(self, node, player, depth, **kwargs):
        
        if self.is_environment_playing(player, **kwargs):
            print("ENVIRONMENT PLAYING", "Depth: ", depth)
            is_open = node.has_open_branch(**kwargs)
            if is_open:
                return is_open

            node_tnf = self.calculate_tnf_with_node(node.formula, **kwargs)
            

            # print("nodo", node.formula, "\n")
            # print(node_tnf.get_all_minimal_X_coverings())
            # if depth == 1:
            #     exit()

            if node_tnf.is_not_X_covering(**kwargs):
                return False
            else:
                all_minimal_X_coverings = node_tnf.get_all_minimal_X_coverings_sorted(**kwargs)
                i_minimal_X_covering = 1
                for minimal_X_covering in all_minimal_X_coverings:
                    i_env_assignment = 1
                    is_open_minimal_covering = Inf
                    for env_assignment, child in minimal_X_covering.items():
                        formula = [AND_OPERATOR, env_assignment, child[0], child[1]]
                        child_node = TableauNode(formula, depth + 1, node)   
                        is_open = self.tableau(child_node, SYSTEM_PLAYING, depth, **kwargs)
                        print("IS_OPEN?",is_open, "For ", env_assignment, i_minimal_X_covering, " / ", len(all_minimal_X_coverings), " minimal X covering and ", i_env_assignment, " / ", len(minimal_X_covering.keys()), "environment assignment",  "Depth: ", depth)
                        i_env_assignment+=1
                        if not is_open:
                            break
                        else:
                            #Mirar aqui si ha habido nodos success con el nodo actual o nodos superiores
                            is_open_minimal_covering = min(is_open_minimal_covering, is_open)
                    if is_open:
                        if is_open_minimal_covering >= depth:
                            self.success_nodes.append(is_open_minimal_covering)
                        return is_open_minimal_covering
                    else:
                        self.failed_nodes.append(TemporalFormula.to_str(node.formula))
                    i_minimal_X_covering += 1
                return False
    
        else:
            print("SYS PLAYING")
            env_assignment = node.formula[1]
            sys_assignments = node.formula[2]
            strict_future_formulas = node.formula[3]
            if strict_future_formulas == [{'X[1]False'}] or sys_assignments == {'False'}:
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
        print(self.safety_formula.ab)
        print(['&', self.safety_formula.ab, self.env_constraints.ab, node])
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


