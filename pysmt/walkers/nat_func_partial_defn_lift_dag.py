from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.typing import INT, NAT

class NatVarLiftDagWalker(IdentityDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        IdentityDagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager