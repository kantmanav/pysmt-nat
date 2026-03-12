from pysmt.walkers.nat_var_lift_dag import NatVarLiftDagWalker
from pysmt.typing import INT, NAT, FunctionType


class NatFuncGlobalDefnLiftDagWalker(NatVarLiftDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        NatVarLiftDagWalker.__init__(self,
                                     env=env,
                                     invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager
        self._lifted_symbols = {}
        self._global_axioms = {}

    def _lift_type(self, type_):
        if type_ is NAT:
            return INT
        if type_.is_function_type():
            # pySMT represents 0-arity "functions" as plain symbols at use sites,
            # so the lifted declaration must collapse to the return sort as well.
            if len(type_.param_types) == 0:
                return self._lift_type(type_.return_type)
            return FunctionType(self._lift_type(type_.return_type),
                                [self._lift_type(p) for p in type_.param_types])
        return type_

    def _get_lifted_symbol(self, symbol):
        lifted = self._lifted_symbols.get(symbol)
        if lifted is not None:
            return lifted

        lifted_type = self._lift_type(symbol.symbol_type())
        if lifted_type == symbol.symbol_type():
            lifted = symbol
        else:
            lifted = self.mgr.Symbol(symbol.symbol_name() + "'", lifted_type)
        self._lifted_symbols[symbol] = lifted
        return lifted

    def _nat_guard(self, term):
        return self.walk_le(None, [self.mgr.Int(0), term])

    def _register_global_axiom(self, symbol, lifted_symbol):
        if symbol in self._global_axioms:
            return

        symbol_type = symbol.symbol_type()
        if (not symbol_type.is_function_type()) or symbol_type.return_type is not NAT:
            return

        quantified_vars = []
        nat_guards = []
        for idx, param_type in enumerate(symbol_type.param_types):
            lifted_param_type = self._lift_type(param_type)
            qvar = self.mgr.FreshSymbol(lifted_param_type,
                                        template="%s!%d'%%d" %
                                        (symbol.symbol_name(), idx))
            quantified_vars.append(qvar)
            if param_type is NAT:
                nat_guards.append(self._nat_guard(qvar))

        # the global lifting strategy constrains Nat-returning functions only on
        # the Nat subdomain of their lifted Int arguments.
        if quantified_vars:
            application = self.mgr.Function(lifted_symbol, quantified_vars)
        else:
            application = lifted_symbol
        consequent = self._nat_guard(application)

        if nat_guards:
            axiom_body = self.walk_implies(None,
                                           [self.walk_and(None, nat_guards),
                                            consequent])
        else:
            axiom_body = consequent

        if quantified_vars:
            axiom = self.mgr.ForAll(quantified_vars, axiom_body)
        else:
            axiom = axiom_body

        self._global_axioms[symbol] = axiom

    def walk(self, formula, **kwargs):
        if formula in self.memoization:
            return self.memoization[formula]

        self._global_axioms = {}

        fvars = list(formula.get_free_variables())
        _, _, guards = self.get_nat_guards(fvars)
        # do not eagerly substitute free Nat variables before walking: function
        # applications must be rewritten together with their lifted signatures to
        # avoid transiently ill-typed terms.
        formula = self.walk_and(None, [formula] + guards)

        res = self.iter_walk(formula, **kwargs)
        if self._global_axioms:
            conjuncts = list(res.args()) if res.is_and() else [res]
            conjuncts.extend(self._global_axioms.values())
            res = self.walk_and(None, conjuncts)

        if self.invalidate_memoization:
            self.memoization.clear()
        return res

    def walk_symbol(self, formula, args, **kwargs):
        lifted = self._get_lifted_symbol(formula)
        symbol_type = formula.symbol_type()
        if symbol_type.is_function_type() and len(symbol_type.param_types) == 0:
            self._register_global_axiom(formula, lifted)
        return lifted

    def walk_function(self, formula, args, **kwargs):
        old_name = formula.function_name()
        new_name = self._get_lifted_symbol(old_name)
        self._register_global_axiom(old_name, new_name)
        return self.mgr.Function(new_name, args)

    def walk_forall(self, formula, args, **kwargs):
        qvars, _, guards = self.get_nat_guards(formula.quantifier_vars())
        if not guards:
            return self.mgr.ForAll(qvars, args[0])
        return self.mgr.ForAll(qvars,
                               self.walk_implies(None,
                                                 [self.walk_and(None, guards),
                                                  args[0]]))

    def walk_exists(self, formula, args, **kwargs):
        qvars, _, guards = self.get_nat_guards(formula.quantifier_vars())
        if not guards:
            return self.mgr.Exists(qvars, args[0])
        return self.mgr.Exists(qvars, self.walk_and(None, guards + [args[0]]))
