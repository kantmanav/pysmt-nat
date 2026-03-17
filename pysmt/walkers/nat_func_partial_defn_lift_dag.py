from pysmt.typing import INT, NAT, FunctionType
from pysmt.walkers.nat_var_lift_dag import NatVarLiftDagWalker


class NatFuncPartialDefnLiftDagWalker(NatVarLiftDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        NatVarLiftDagWalker.__init__(self,
                                     env=env,
                                     invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager
        self._lifted_symbols = {}
        self._pending_guards = {}

    def _lift_type(self, type_):
        if type_ is NAT:
            return INT
        if type_.is_function_type():
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

    def _dedupe_guards(self, guards):
        return list(dict.fromkeys(guards))

    def _collect_child_guards(self, formula, **kwargs):
        guards = []
        for child in self._get_children(formula):
            key = self._get_key(child, **kwargs)
            guards.extend(self._pending_guards.get(key, ()))
        return self._dedupe_guards(guards)

    def _get_own_guards(self, formula, translated):
        if formula.is_function_application():
            if formula.function_name().symbol_type().return_type is NAT:
                return [self._nat_guard(translated)]
            return []

        if formula.is_symbol():
            symbol_type = formula.symbol_type()
            if symbol_type.is_function_type() and \
               len(symbol_type.param_types) == 0 and \
               symbol_type.return_type is NAT:
                return [self._nat_guard(translated)]
        return []

    def _compute_node_result(self, formula, **kwargs):
        key = self._get_key(formula, **kwargs)
        if key in self.memoization:
            return

        try:
            fun = self.functions[formula.node_type()]
        except KeyError:
            fun = self.walk_error

        args = [self.memoization[self._get_key(s, **kwargs)]
                for s in self._get_children(formula)]
        result = fun(formula, args=args, **kwargs)

        guards = self._collect_child_guards(formula, **kwargs)
        guards.extend(self._get_own_guards(formula, result))
        guards = self._dedupe_guards(guards)

        if result.get_type().is_bool_type() and guards:
            result = self.walk_and(None, guards + [result])
            guards = []

        self.memoization[key] = result
        self._pending_guards[key] = guards

    def walk(self, formula, **kwargs):
        if formula in self.memoization:
            return self.memoization[formula]

        self._pending_guards = {}

        fvars = list(formula.get_free_variables())
        _, _, guards = self.get_nat_guards(fvars)
        formula = self.walk_and(None, [formula] + guards)

        res = self.iter_walk(formula, **kwargs)
        pending = self._pending_guards.get(self._get_key(formula, **kwargs), [])
        if pending:
            res = self.walk_and(None, pending + [res])

        if self.invalidate_memoization:
            self.memoization.clear()
            self._pending_guards.clear()
        return res

    def walk_nat_constant(self, formula, args, **kwargs):
        return self.mgr.Int(formula.constant_value())

    def walk_symbol(self, formula, args, **kwargs):
        return self._get_lifted_symbol(formula)

    def walk_function(self, formula, args, **kwargs):
        old_name = formula.function_name()
        new_name = self._get_lifted_symbol(old_name)
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
