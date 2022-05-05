from temporal_formula import neg_literal


def get_env_minimal_covering(all_assignments, valid_assignments):
    if not valid_assignments:
        return all_assignments
    env_minimal_covering = list()
    for assignment in all_assignments:
        if is_valid_assignment(assignment, valid_assignments):
            env_minimal_covering.append(assignment)
    return env_minimal_covering


def is_valid_assignment(assignment, valid_assignments):
    for valid_assignment in valid_assignments:
        valid = True
        neg_literals_valid_assignment = [ neg_literal(env_literal) for env_literal in assignment]
        for neg_literal_valid_assignment in neg_literals_valid_assignment:
            if neg_literal_valid_assignment in valid_assignment:
                valid = False
                break
        if not valid:
            continue
        else:
            return True
    return False