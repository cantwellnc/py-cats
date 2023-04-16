from functools import singledispatchmethod
from itertools import product
from typing import Any, Callable, Iterable, Optional, Set

from icontract import ensure, require

from colors import Colors


class Ob:
    def __init__(self, name: str, _type: type, value: Iterable) -> None:
        self.name = name
        self._type = _type
        self.value = value


def dom_is_subset_of_codom(
    name: str,
    dom: Ob,
    codom: Ob,
    fn: Callable,
) -> Optional[bool]:
    if all([fn(val) in codom.value for val in dom.value]):
        return True
    raise ImageIsNotSubsetOfCodom(dom, codom, name)


def type_of_dom_matches_type_of_codom(dom: Ob, codom: Ob) -> bool:
    return dom._type == codom._type


class ImageIsNotSubsetOfCodom(Exception):
    def __init__(self, dom: Ob, codom: Ob, fn_name: str) -> None:
        super().__init__(
            f"{Colors.FAIL} The image of {dom.name} under {fn_name} must be a subset of {codom.name} {Colors.ENDC}"
        )


class Hom(Callable):
    @require(type_of_dom_matches_type_of_codom)
    @ensure(dom_is_subset_of_codom)
    def __init__(self, name: str, dom: Ob, codom: Ob, fn: Callable) -> None:
        # TODO: (fix) this is assuming that objects are always Iterables. Not necessarily the case.
        self.name = name
        self.dom = dom
        self.codom = codom
        self.fn = fn

    def __hash__(self) -> int:
        return hash(self.name + self.dom.name + self.codom.name)

    def __call__(self, src: Ob):
        # TODO: (fix) this is assuming that objects are always Iterables. Not necessarily the case.
        return {self.fn(val) for val in src.value}

    def __eq__(self, other) -> bool:
        return (
            self.dom == other.dom
            and self.codom == other.codom
            and {self.fn(val) for val in self.dom.value}
            == {other.fn(val) for val in other.dom.value}
        )


class NotComposable(Exception):
    def __init__(self, f: Hom, g: Hom) -> None:
        super().__init__(
            f"{Colors.FAIL} Unable to form the composition {f.name};{g.name}. The codomain of f must match the domain of g."
            f"The codomain of {f.name} was {f.codom} != {g.dom}, the domain of {g.name}"
            f"{Colors.ENDC}"
        )


def homs_are_composable(f: Hom, g: Hom) -> Optional[bool]:
    if f.codom == g.dom:
        return True
    raise NotComposable(f, g)


class Category:
    def __init__(self, obs: Set[Ob], homs: Set[Hom]) -> None:
        self.obs = obs
        self.id_homs = {ob: Hom(f"id_{ob.name}", ob, ob, lambda x: x) for ob in obs}
        self.homs = homs.union(self.id_homs.values())

        # Category axioms
        # associativity 
        for f, g, h in product(homs, homs, homs): 
            if f.codom == g.dom and g.codom == h.dom:
                assert self.compose(self.compose(f, g), h) == self.compose(
                    f, self.compose(g, h)
                )
        # identity
        for f in homs:
            id_dom = self.id_homs[f.dom]
            id_codom = self.id_homs[f.codom]
            assert self.compose(id_dom, f) == self.compose(f, id_codom)

    @require(homs_are_composable)
    def compose(self, f: Hom, g: Hom) -> Hom:
        """Returns a new Hom that is the functional composite of the inputs.
        We use the notation f;g to denote the composition of f and g. This is
        read as 'do f, then do g'."""
        if f in self.id_homs:
            return g
        if g in self.id_homs:
            return f
        composite = Hom(f"{f.name};{g.name}", f.dom, g.codom, lambda x: g.fn(f.fn(x)))
        self.homs.add(composite)
        return composite


class Functor:
    def __init__(
        self,
        dom: Category,
        codom: Category,
        map_on_obs: Callable,
        map_on_homs: Callable,
    ) -> None:
        self.dom = dom
        self.codom = codom
        self.map_on_obs = map_on_obs
        self.map_on_homs = map_on_homs

        # check the functor axioms
        # F(id_a) = id_F(a)
        for ob, id_hom in dom.id_homs.items():
            # pointwise comparison; have to descend to underlying fns
            # TODO: (fix) this is assuming that objects are always Iterables. Not necessarily the case.
            for val in ob.value:
                assert map_on_homs(id_hom.fn(val)) == codom.id_homs[map_on_obs(ob)].fn(
                    val
                )

        # F(f;g) = F(g);F(g)
        for f, g in product(dom.homs, dom.homs):
            # only check for composable morphisms
            if f.codom == g.dom:
                for val in f.dom.value:
                    assert map_on_homs(dom.compose(f, g).fn(val)) == codom.compose(
                        map_on_homs(f), map_on_homs(g)
                    ).fn(val)

    @singledispatchmethod
    def __call__(self, arg: Any):
        print("calling...")

    @__call__.register
    def _(self, arg: Ob) -> Ob:
        "inside ob call"
        return self.map_on_obs(arg)

    @__call__.register
    def _(self, arg: Hom) -> Hom:
        return self.map_on_homs(arg)


if __name__ == "__main__":
    # some sanity checks...
    a = Ob("A", set, {1, 2})
    b = Ob("B", set, {1})
    hom_a_b = Hom("f", a, b, lambda x: 1)
    C = Category({a, b}, {hom_a_b})
    print(hom_a_b(a))
    print("hom_a_b: ", C.compose(C.id_homs[a], hom_a_b)(a))
    print("hom_a_b: ", C.compose(hom_a_b, C.id_homs[b])(a))

    hom_b_a = Hom("g", b, a, lambda x: 2)
    C = Category({a, b}, {hom_b_a})
    print(hom_b_a(a))
    print("hom_b_a: ", C.compose(C.id_homs[b], hom_b_a)(b))
    print("hom_b_a: ", C.compose(hom_b_a, C.id_homs[a])(b))

    id_functor = Functor(C, C, lambda x: x, lambda x: x)

    print(
        f"""Applying id_functor to object {a.name} with value: {a.value} results in the object {id_functor(a).name} with value {id_functor(a).value}"""
    )

    D = Category({a, b}, {hom_a_b, hom_b_a})

    print(D.compose(hom_b_a, hom_a_b)(b))

    # Example of a contract violation
    d = Ob("D", set, {1, 2, 3})
    # Hom("hom_a_d", a,d, lambda x: 1 if x == 1 else 5) 
    # ^^ (This will throw an ImageIsNotSubsetOfCodom exception.)

    C.compose(hom_a_b, hom_a_b)
