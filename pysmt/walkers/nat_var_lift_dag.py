from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.typing import INT, NAT

class NatVarLiftDagWalker(IdentityDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        IdentityDagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager

    def get_nat_guards(self, vars):
        vars = set(vars)
        var_subs = {}
        guards = []
        for v in vars:
            if v.symbol_type() is NAT:
                v_new = self.mgr.Symbol(v.symbol_name() + "'", INT)
                var_subs[v] = v_new
                guards.append(self.walk_le(None, [self.mgr.Int(0), v_new]))
        for v, v_new in var_subs.items():
            vars.remove(v)
            vars.add(v_new)
        return list(vars), var_subs, guards

    def walk(self, formula, **kwargs):
        if formula in self.memoization:
            return self.memoization[formula]

        fvars = list(formula.get_free_variables())
        fvars, fvar_subs, guards = self.get_nat_guards(fvars)
        conjuncts = []
        conjuncts.append(formula.substitute(fvar_subs))
        conjuncts.extend(guards)
        formula = self.walk_and(None, conjuncts)

        res = self.iter_walk(formula, **kwargs)

        if self.invalidate_memoization:
            self.memoization.clear()
        return res

    def walk_forall(self, formula, args, **kwargs):
        qvars = formula.quantifier_vars()
        qvars, qvar_subs, guards = self.get_nat_guards(qvars)
        if not guards:
            return self.mgr.ForAll(qvars, args[0])
        else:
            return self.mgr.ForAll(qvars, self.walk_implies(None, [self.walk_and(None, guards), args[0].substitute(qvar_subs)]))

    def walk_exists(self, formula, args, **kwargs):
        qvars = formula.quantifier_vars()
        qvars, qvar_subs, guards = self.get_nat_guards(qvars)
        if not guards:
            return self.mgr.Exists(qvars, args[0])
        else:
            conjuncts = []
            conjuncts.extend(guards)
            conjuncts.append(args[0].substitute(qvar_subs))
            return self.mgr.Exists(qvars, self.walk_and(None, conjuncts))