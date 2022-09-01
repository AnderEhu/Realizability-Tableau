import itertools


from TemporalFormula.src.temporal_formula import AUX_NODE, NEG_AUX_NODE, OR_OPERATOR, TemporalFormula


class MinimalCovering:

    def __init__(self):
        pass

    @staticmethod
    def is_not_X_covering(tnf_formula):
        for _, value in tnf_formula.items():
            if value == [[{'False'}, [{'X[1]False'}]]]:
                return True
        return False

    
    @staticmethod
    def sort_minimal_coverings(tnf_formula):
        """
        Given a minimal covering returns its score. The scoring is based on strict-future formulas as follows:
            - Add score for every disjuction of set of futures. In particular, number of set of futures multiplied by 100
            - Add big score whether 'X[1]True' is between the futures
            - Substract score for every futures based of how large its the conjuction of futures.
        """
        env_valuations_with_sorted_strict_futures = dict()
        env_valuations_scores = list()
        for env_valuation, moves in tnf_formula.items():
            moves_score = list()
            sum_score_env_valuation = 0
            for move in moves:
                move_score = MinimalCovering.score_move_futures(move)
                moves_score.append(move_score)
                sum_score_env_valuation+=move_score
            moves_sorted = [i for _,i in sorted(zip(moves_score,moves), reverse=True)]
            env_valuations_scores.append((sum_score_env_valuation, env_valuation))
            env_valuations_with_sorted_strict_futures[env_valuation] = moves_sorted

        env_valuations_sorted = [i for _,i in sorted(env_valuations_scores, reverse=True)]
        tnf_sorted = list()
        for env_valuation in env_valuations_sorted:
            print(env_valuation, env_valuations_with_sorted_strict_futures[env_valuation])
            tnf_sorted.append(env_valuations_with_sorted_strict_futures[env_valuation])
        return env_valuations_sorted, itertools.product(*tnf_sorted)



    @staticmethod 
    def score_move_futures(move):
        score = 0
        OR_futures = move[1]
        score+=len(OR_futures)*1000
        for AND_futures in OR_futures:
            if AND_futures == {'X[1]True'}:
                score+=10000000000000
            else:
                score -= len(AND_futures)*100
                for future in AND_futures:
                   score+=MinimalCovering.score_future_interval(future)
        return score

    @staticmethod
    def score_future_interval(formula: str):
        formula_splitted = formula.split("]")
        score = 0
        is_neg = False

        for f in formula_splitted:
            f = f + "]"
            if TemporalFormula.is_neg(f[0]):
                f = f[1:]
                is_neg = True
            if f[0] == "(":
                f = f[1:]

            if TemporalFormula.is_next(f):
                next_n = TemporalFormula.get_next_n(f)
                score -= next_n^3
            if TemporalFormula.is_eventually(f):
                F_G_inf_interval, F_G_sup_interval = TemporalFormula.get_eventually_always_op_limits(f)
                if is_neg:
                    score -= (F_G_sup_interval-F_G_inf_interval) - F_G_inf_interval
                else:
                    score += (F_G_sup_interval-F_G_inf_interval) - F_G_inf_interval

            if TemporalFormula.is_always(f):
                F_G_inf_interval, F_G_sup_interval = TemporalFormula.get_eventually_always_op_limits(f)
                if is_neg:
                    score += (F_G_sup_interval-F_G_inf_interval) - F_G_inf_interval
                else:
                    score -= (F_G_sup_interval-F_G_inf_interval) - F_G_inf_interval

        return score


