import pytest
from Tableau.src.tableau import Tableau

from tools import read_benchmark_file


developair_benchmarks_path = {
    "benchmarks/Developair/benchmark4.txt",
    "benchmarks/Developair/benchmark5.txt",
    "benchmarks/Developair/benchmark6.txt",
    "benchmarks/Developair/cooker.txt",


}
@pytest.mark.parametrize(
    "path", developair_benchmarks_path
)

def test_tnf_developair(path):
    initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
    tableau = Tableau(initial_formula, safety_formula, env_constraints)
    assert tableau.is_open