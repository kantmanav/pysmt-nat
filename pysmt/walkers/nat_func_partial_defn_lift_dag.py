from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.walkers.nat_var_lift_dag import NatVarLiftDagWalker
from pysmt.typing import INT, NAT, BOOL, FunctionType
from pysmt.fnode import FNode
from dataclasses import dataclass

@dataclass(frozen=True)
class R:
    node: FNode
    pending_guards: tuple[FNode, ...]

class NatFuncPartialDefnLiftDagWalker(NatVarLiftDagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        IdentityDagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager
        self.lifted_symbols = {}
        self.func_guards = []
        self.identity_dag_walker = IdentityDagWalker(env=self.env)

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

    # Takes args of type R, extracts the nodes and guards for manipulation by walk_* methods
    def _get_child_nodes_and_guards(self, args):
        nodes = [a.node for a in args]
        guards = [g for a in args for g in a.pending_guards]
        return nodes, guards

    def walk(self, formula, **kwargs):
        if formula in self.memoization:
            return self.memoization[formula]

        fvars = list(formula.get_free_variables())
        _, _, guards = self.get_nat_guards(fvars)
        formula = self.walk_and(None, [formula] + guards)

        res = self.iter_walk(formula, **kwargs)

        if self.invalidate_memoization:
            self.memoization.clear()
        return res

    def translate(self, formula, **kwargs):
        return self.walk(formula, **kwargs).node

    def walk_symbol(self, formula, args, **kwargs):
        lifted = self._get_lifted_symbol(formula)
        symbol_type = formula.symbol_type()
        if symbol_type.is_function_type() and len(symbol_type.param_types) == 0:
            self._register_global_axiom(formula, lifted)
        return R(node=lifted, pending_guards=())

    def walk_function(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)

        old_name, old_ret_type = formula.function_name(), formula.symbol_type().return_type
        new_name = self._get_lifted_symbol(old_name)
        func = self.mgr.Function(new_name, c_nodes)
        if old_ret_type is BOOL:
            return R(node=self.walk_and(None, guards + [func]), pending_guards=())
        elif old_ret_type is NAT:
            guards.append(self._nat_guard(formula))
        return R(node=func, pending_guards=tuple(guards))

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

    # Add guards to bool types whose arguments are not themselves bools
    def walk_equals(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)

        eq = self.mgr.Equals(c_nodes[0], c_nodes[1])
        return R(node=self.walk_and(None, guards + [eq]), pending_guards=())

    # def walk_le(self, formula, args, **kwargs):
    #     return self.mgr.LE(args[0], args[1])

    # def walk_lt(self, formula, args, **kwargs):
    #     return self.mgr.LT(args[0], args[1])