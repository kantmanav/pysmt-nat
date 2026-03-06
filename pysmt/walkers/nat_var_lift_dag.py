from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.typing import INT, NAT

class NatVarLiftDagWalker(IdentityDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        IdentityDagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager

    def walk_forall(self, formula, args, **kwargs):
        qvars = []
        guards = []
        for v in formula.quantifier_vars():
            if v.symbol_type() is NAT:
                v_new = self.mgr.Symbol(v.symbol_name() + "'", INT)
                qvars.append(v_new)
                guards.append(self.walk_le(None, [self.mgr.Int(0), v_new]))
            else:
                qvars.append(v)
        if not guards:
            return self.mgr.ForAll(qvars, args[0])
        else:
            return self.mgr.ForAll(qvars, self.walk_implies(None, [self.walk_and(None, guards), args[0]]))
