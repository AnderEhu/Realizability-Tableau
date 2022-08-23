from TemporalFormula.src.temporal_formula import TemporalFormula
from tools import analysis


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

    def is_implicated_by_success_nodes(self, success_nodes, strToAb):
        if success_nodes is None:
            return False
        for success_node in success_nodes:
            if self.is_implicated_by_a_success_node(success_node, strToAb):
                return True
        return False
        
    def is_implicated_by_a_success_node(self, success_node, strToAb):
        success_node_ab = strToAb[success_node]
        if TemporalFormula.is_implicated(success_node_ab, self.formula):
            return True
        else:
            return False

    def implicate_a_failure_nodes(self, failure_nodes, strToAb):
        if failure_nodes is None:
            return False
        for failure_node in failure_nodes:
            if self.implicate_a_failure_node(failure_node, strToAb):
                return True
        return False

    def implicate_a_failure_node(self, failure_node, strToAb):
        failure_node_ab = strToAb[failure_node]
        if TemporalFormula.is_implicated(self.formula, failure_node_ab):
            print("FAILURE: ", self.formula, "IS IMPLICATED", failure_node_ab)
            return True
        else:
            return False

    def success_previous_node(self, success_node, strToAb):
        return self.__success_previuos_node(self.previous_node, success_node, strToAb)
    
    def __success_previuos_node(self, node, success_node, strToAb):
        if node is None:
            return False
        if not node.previous_node:
            success_node_ab = TemporalFormula.getStrToAb(success_node, strToAb)
            if TemporalFormula.is_implicated(success_node_ab, node.formula):
                return node.depth
            else:
                return False

        else:
            success_previous = self.__success_previuos_node(node.previous_node, success_node, strToAb)
            if success_previous:
                return success_previous
            else:
                success_node_ab = TemporalFormula.getStrToAb(success_node, strToAb)
                if TemporalFormula.is_implicated(success_node_ab, node.formula):
                    return node.depth
                else:
                    return False

    def failed_previous_node(self, failed_node, strToAb):
        return self.__failed_previuos_node(self.previous_node, failed_node, strToAb)

    def __failed_previuos_node(self, node, failed_node, strToAb):
        if node is None:
            return False
        if not node.previous_node:
            failed_node_ab = TemporalFormula.getStrToAb(failed_node, strToAb)
            if TemporalFormula.is_implicated(node.formula, failed_node_ab):
                return node.depth
            else:
                return False

        else:
            success_previous = self.__success_previuos_node(node.previous_node, failed_node, strToAb)
            if success_previous:
                return success_previous
            else:
                failed_node_ab = TemporalFormula.getStrToAb(failed_node, strToAb)
                if TemporalFormula.is_implicated(node.formula, failed_node_ab):
                    return node.depth
                else:
                    return False

            
            

        


