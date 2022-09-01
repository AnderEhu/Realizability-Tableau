import pytest
from Tableau.src.tableau import Tableau

from tools import read_benchmark_file


developair_benchmarks_path = {
    "benchmarks/Overleaf/benchmark1.txt",
}
@pytest.mark.parametrize(
    "path", developair_benchmarks_path
)

def test_tnf_overleaf(path):
    initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
    tableau = Tableau(initial_formula, safety_formula, env_constraints)
    assert tableau.is_open