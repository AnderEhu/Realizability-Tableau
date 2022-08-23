import copy
import itertools

from TemporalFormula.src.temporal_formula import TemporalFormula


class MinimalCovering:

    def __init__(self):
        pass

    @staticmethod
    def is_not_X_covering(tnf_formula, **kwargs):
        for _, value in tnf_formula.items():
            if value == list():
                return True
        return False

    @staticmethod
    def get_all_minimal_X_coverings(tnf_formula, env_minimal_covering, subsumptions = False, **kwargs):
        
        assignments_last_index = MinimalCovering.get_assignments_last_indices(tnf_formula, **kwargs)

        actual_minimal_covering_indexes = list(itertools.repeat ( 0, len(tnf_formula)))

        all_minimal_X_coverings = list()

        increment_index = 0

        while increment_index < len(tnf_formula):
            actual_minimal_covering = dict()
            for i, value_i in enumerate(actual_minimal_covering_indexes):
            
                assignment_i = frozenset(env_minimal_covering[i])
                actual_minimal_covering[assignment_i] = tnf_formula[assignment_i][value_i]

            if subsumptions:
                all_minimal_X_coverings.append(MinimalCovering.minimal_covering_with_subsumptions(actual_minimal_covering))
            else:
                all_minimal_X_coverings.append(actual_minimal_covering)
            
      
            while increment_index < len(tnf_formula) and actual_minimal_covering_indexes[increment_index] >= assignments_last_index[increment_index]:
                increment_index+=1

            if increment_index < len(tnf_formula) and actual_minimal_covering_indexes[increment_index] < assignments_last_index[increment_index]:
                actual_minimal_covering_indexes[increment_index] += 1
        
        return all_minimal_X_coverings

    @staticmethod
    def minimal_covering_with_subsumptions(minimal_covering):
        minimal_covering_subsumptions = dict()
        for env_assignment, child in minimal_covering.items():
            child_with_subsumptions = [list(), list()]
            child_with_subsumptions[0] = child[0]
            for and_futures in child[1]:
                futures_with_subsumptions = copy.deepcopy(and_futures)
                for future1 in and_futures:
                    for future2 in and_futures:
                        if future1 == future2:
                            continue
                        if TemporalFormula.subsumes(future1, future2):
                            futures_with_subsumptions.remove(future2)
                        elif TemporalFormula.subsumes(future2, future1):
                            futures_with_subsumptions.remove(future1)
                        else:
                            continue
                child_with_subsumptions[1].append(futures_with_subsumptions)
            minimal_covering_subsumptions[env_assignment] = child_with_subsumptions
        return minimal_covering_subsumptions

    @staticmethod
    def  get_assignments_last_indices(self, tnf, **kwargs):
        res = list()
        for _, value in tnf.items():
            res.append(len(value)-1)

        return res


    @staticmethod
    def get_all_minimal_X_coverings_sorted(self, **kwargs):
        all_minimal_coverings = self.get_all_minimal_X_coverings(subsumptions = False)
        sorted_minimal_coverings = MinimalCovering.sort_by_score_all_minimal_X_coverings(all_minimal_coverings)
                

        return sorted_minimal_coverings

    @staticmethod
    def sort_by_score_all_minimal_X_coverings(all_minimal_coverings):
        scores = dict()
        for i, minimal_X_covering in enumerate(all_minimal_coverings):
            minimal_X_covering_score = MinimalCovering.score_minimal_covering(minimal_X_covering)
            scores[i] = minimal_X_covering_score
        
        sorted_scores = sorted(scores.items(), key=lambda x: x[1], reverse=True)

        print(sorted_scores)

        minimal_coverings_sorted_by_score = [all_minimal_coverings[i[0]] for i in sorted_scores]

        return minimal_coverings_sorted_by_score


    @staticmethod
    def score_minimal_covering(minimal_X_covering):
        score = 0
        for _, child in minimal_X_covering.items():
            futures = child[1]
            score+=len(futures)*5
            for future in futures:
                if future == {'XTrue'}:
                    score+=10000
                else:
                    score -= len(future)


        return score