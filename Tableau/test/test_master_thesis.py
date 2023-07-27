import pytest
from Tableau.src.tableau import Tableau

from tools import read_benchmark_file


expected_results = {
    "benchmarks/Overleaf/benchmark1.txt" : True,
    "benchmarks/Overleaf/benchmark2.txt" : False,
    "benchmarks/Overleaf/benchmark3.txt" : True,
    "benchmarks/Overleaf/benchmark4.txt" : True,
    "benchmarks/Overleaf/benchmark5.txt" : True,
    "benchmarks/Overleaf/benchmark6.txt" : False,
    "benchmarks/Overleaf/benchmark7.txt" : True,

    
}
@pytest.mark.parametrize(
    "path, expected_result", [(key, value) for key, value in expected_results.items()]
)

def test_tnf_overleaf(path, expected_result):
    initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
    tableau = Tableau(initial_formula, safety_formula, env_constraints)
    assert expected_result == tableau.is_open


# realizable_automatic_path = glob.glob("benchmarks/Automatic/Realizable/*.txt")
# @pytest.mark.parametrize(
#     "path", realizable_automatic_path
# )
# def test_automatic_realizable_benchmarks(path):
#     initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
#     tableau = Tableau(initial_formula, safety_formula, env_constraints)
#     assert tableau.is_open

# unrealizable_automatic_path = glob.glob("benchmarks/Automatic/Unrealizable/*.txt")
# @pytest.mark.parametrize(
#     "path", unrealizable_automatic_path
# )
# def test_automatic_unrealizable_benchmarks(path):
#     initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
#     tableau = Tableau(initial_formula, safety_formula, env_constraints)
#     assert not tableau.is_open


