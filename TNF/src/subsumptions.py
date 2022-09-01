
from Solver.bica import prime_cover_via_BICA
from TNF.src.inconsistencies import Inconsistencies
from TemporalFormula.src.temporal_formula import TemporalFormula
from tools import analysis


class Subsumptions:

    def __init__(self):
        pass

    @staticmethod
    def list_futures_set_with_futures_set(union_futures, futures_i):
        """
        Given union_futures(a list of futures sets) and future_i (a futures set), futures_i is add to union_futures applying the following subsumptions:
            - If union_futures contains a weaker futures set, then futures_i will not be added.
            - For every futures set in union_futures weaker than given future_i will be deleted and, then, future_i will be add 
            - If there is not subsumptions between union_futures, future_i will be added.

        Args: 
            union_futures: List of futures sets
            future_i: set of futures

        Example:
            - [{Xs, Xp, Xq}, {Xs, Xp}] and {Xs} union_futures will be [{Xs}] due to the fact that {Xs} is weaker than {Xs, Xp, Xq} and {Xs, Xp}
            - [{Xp}] and {Xs, Xp, Xq} union_futures will be [{Xs}] because {Xp} is weaker than {Xs, Xp, Xq}
            - [{Xs, Xp, Xq}, {Xs, Xp}] and {Xg} union_futures will be[{Xs, Xp, Xq}, {Xs, Xp}, {Xg}]

    
        """
        assert union_futures and futures_i
        if futures_i in union_futures:
            return
        elif futures_i == {'X[1]True'}: # {'X[1]True'} is the weakest futures set
            union_futures.clear()
            union_futures.append(futures_i)
        elif union_futures == [{'X[1]True'}]: # {'X[1]True'} is the weakest futures set
            return
        else:
            remove_futures = list()
            for futures_j in union_futures:
                #if any futures set of union_futures is weaker than given futures set (futures_i), then, futures_i is subsumed
                if futures_j <= futures_i: 
                    return    
                # If given futures set (futures_i) is weaker  any futures set of union_futures (futures_j),
                # save at remove_future list for deleting later because future_i could subsumes more futures sets
                elif futures_i < futures_j: 
                    remove_futures.append(futures_j)
            # Remove detected subsumptions in union_futures
            for set_futures in remove_futures:
                union_futures.remove(set_futures)
                
            #Once stronger futures set of union_futures detect and deleted from union_futures, add future_i
            union_futures.append(futures_i)

    @staticmethod
    def is_list_futures_set_weaker(list_futures_set_1, list_futures_set_2):
        """
        Given two list of futures sets, list_futures_set_1 and list_futures_set_2, list_futures_set_1 is weakear than list_futures_set_2
        iff for every futures set of list_futures_set_2 there is a weaker futures set in list_futures_set_1.
        """
        
        if list_futures_set_1 == [{'X[1]True'}]:
            return True
        
        if list_futures_set_2 == [{'X[1]True'}]:
            return False
        
        if list_futures_set_1 == list_futures_set_2:
            return True
        move_1_weaker_move_2 = True
        for set_futures_2_i in list_futures_set_2:
            is_set_futures_1_weaker = False
            for set_futures_1_i in list_futures_set_1:
                if set_futures_1_i <= set_futures_2_i:
                    is_set_futures_1_weaker = True
                    break
            if not is_set_futures_1_weaker:
                move_1_weaker_move_2 = False
                break
        return move_1_weaker_move_2

    @staticmethod
    def move_lists_with_move(list_of_moves, new_move):

        if list_of_moves == [{'X[1]True'}]:
            return
        
        futures_new_move = new_move[1]

        if futures_new_move == [{'X[1]True'}]:
            list_of_moves.clear()
            list_of_moves.append(new_move)


        for move_i in list_of_moves:
            futures_move_i = move_i[1]
            if Subsumptions.is_list_futures_set_weaker(futures_new_move, futures_move_i):
                list_of_moves.remove(move_i)
            elif Subsumptions.is_list_futures_set_weaker(futures_move_i, futures_new_move):
                return
        
        list_of_moves.append(new_move)

    @staticmethod
    @analysis
    def is_implicated(formula_1_ab, formula_2_ab, **kwargs):
        """
            Returns if formula_1_ab (temporal formula) subsume formula_2_ab (temporal formula) , ej G[0,4]a subsumes G[0,1]a
            Args:
                -formula_1_ab: temporal formula as a list of lists
                -formula_2_ab: temporal formula as a list of lists

            Returns:
                True, if formula_1_ab subsumes formula_2_ab, otherwise, False

        """
        if formula_1_ab == formula_2_ab:
            return True
        neg_formula_2_ab = TemporalFormula.neg_formula_ab(formula_2_ab, changeNegAlwaysEventually=False, **kwargs)
        possible_contradiction = ['&', formula_1_ab, neg_formula_2_ab]

        is_sat = TemporalFormula.is_sat(possible_contradiction)
        if not is_sat:
            return True

        prime_implicants = prime_cover_via_BICA(possible_contradiction)
        fix_prime_implacants = Inconsistencies.delete_inconsistent_sets(prime_implicants)

        if not fix_prime_implacants:
            return True
        else:
            #print("VALID: ", prime_implicants)
            return False
