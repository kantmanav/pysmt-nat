from pysmt.smtlib.parser import get_formula
from  pysmt.shortcuts import get_env
import pysmt as ps
from io import StringIO
class SuspendTypeChecking(object):
    """Context to disable type-checking during formula creation."""

    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager

    def __enter__(self):
        """Entering a Context: Disable type-checking."""
        self.mgr._do_type_check = lambda x : x
        return self.env

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exiting the Context: Re-enable type-checking."""
        self.mgr._do_type_check = self.mgr._do_type_check_real

smtlib_content = """
(declare-fun x () Int)
(assert (= 3 x))
"""

formula = get_formula(StringIO(smtlib_content))
print(formula)

    
