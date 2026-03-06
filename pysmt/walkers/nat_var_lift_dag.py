from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.typing import INT, NAT

class NatVarLiftDagWalker(IdentityDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        IdentityDagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager

    def get_nat_guards(self, formula):
        qvars = set(formula.quantifier_vars())
        qvar_subs = {}
        guards = []
        for v in qvars:
            if v.symbol_type() is NAT:
                v_new = self.mgr.Symbol(v.symbol_name() + "'", INT)
                qvar_subs[v] = v_new
                guards.append(self.walk_le(None, [self.mgr.Int(0), v_new]))
        for v, v_new in qvar_subs.items():
            qvars.remove(v)
            qvars.add(v_new)
        return qvars, qvar_subs, guards

    def walk_forall(self, formula, args, **kwargs):
        qvars, qvar_subs, guards = self.get_nat_guards(formula)
        qvars = list(qvars)
        if not guards:
            return self.mgr.ForAll(qvars, args[0])
        else:
            return self.mgr.ForAll(qvars, self.walk_implies(None, [self.walk_and(None, guards), args[0].substitute(qvar_subs)]))

    def walk_exists(self, formula, args, **kwargs):
        qvars, qvar_subs, guards = self.get_nat_guards(formula)
        qvars = list(qvars)
        if not guards:
            return self.mgr.Exists(qvars, args[0])
        else:
            conjuncts = []
            conjuncts.extend(guards)
            conjuncts.append(args[0].substitute(qvar_subs))
            return self.mgr.Exists(qvars, self.walk_and(None, conjuncts))