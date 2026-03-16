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
        self._lifted_symbols = {}
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
        nodes, guards = [], []
        for a in args:
            if type(a) == FNode:
                nodes.append(a)
            elif type(a) == R:
                nodes.append(a.node)
                guards.extend(a.pending_guards)
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
        return R(node=lifted, pending_guards=())

    def walk_int_constant(self, formula, args, **kwargs):
        return R(node=self.mgr.Int(formula.constant_value()), pending_guards=())

    def walk_and(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.And(c_nodes), pending_guards=())

    def walk_or(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Or(c_nodes), pending_guards=())

    def walk_not(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Not(c_nodes[0]), pending_guards=())

    def walk_iff(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Iff(c_nodes[0], c_nodes[1]), pending_guards=())

    def walk_implies(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Implies(c_nodes[0], c_nodes[1]), pending_guards=())

    def walk_equals(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        eq = self.mgr.Equals(c_nodes[0], c_nodes[1])
        return R(node=self.walk_and(None, guards + [eq]), pending_guards=())

    def walk_ite(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Ite(c_nodes[0], c_nodes[1], c_nodes[2]), pending_guards=())

    def walk_le(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        le = self.mgr.LE(c_nodes[0], c_nodes[1])
        return R(node=self.walk_and(None, guards + [le]), pending_guards=())

    def walk_lt(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        lt = self.mgr.LT(c_nodes[0], c_nodes[1])
        return R(node=self.walk_and(None, guards + [lt]), pending_guards=())

    def walk_forall(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        qvars, _, guards = self.get_nat_guards(formula.quantifier_vars())
        if not guards:
            return R(node=self.mgr.ForAll(qvars, c_nodes[0]), pending_guards=())
        return R(node=self.mgr.ForAll(qvars,
                               self.walk_implies(None,
                                                 [self.walk_and(None, guards),
                                                  args[0]])),
                 pending_guards=())

    def walk_exists(self, formula, args, **kwargs):
        c_nodes, _ = self._get_child_nodes_and_guards(args)
        qvars, _, guards = self.get_nat_guards(formula.quantifier_vars())
        if not guards:
            return R(node=self.mgr.Exists(qvars, c_nodes[0]), pending_guards=())
        return R(node=self.mgr.Exists(qvars, self.walk_and(None, guards + [args[0]])), pending_guards=())

    def walk_plus(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Plus(c_nodes), pending_guards=guards)

    def walk_times(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Times(c_nodes), pending_guards=guards)

    def walk_pow(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Pow(c_nodes[0], c_nodes[1]), pending_guards=guards)

    def walk_minus(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Minus(c_nodes[0], c_nodes[1]), pending_guards=guards)

    def walk_function(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        old_name = formula.function_name()
        old_ret_type = old_name.symbol_type().return_type
        new_name = self._get_lifted_symbol(old_name)
        func_app = self.mgr.Function(new_name, c_nodes)
        if old_ret_type is BOOL:
            return R(node=self.walk_and(None, guards + [func_app]), pending_guards=())
        elif old_ret_type is NAT:
            guards.append(self._nat_guard(func_app))
        return R(node=func_app, pending_guards=tuple(guards))

    def walk_div(self, formula, args, **kwargs):
        c_nodes, guards = self._get_child_nodes_and_guards(args)
        return R(node=self.mgr.Div(c_nodes[0], c_nodes[1]), pending_guards=guards)