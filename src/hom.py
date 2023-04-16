from typing import Callable, Optional

from icontract import ensure, require

from colors import Colors
from ob import Ob


class ImageIsNotSubsetOfCodom(Exception):
    def __init__(self, dom: Ob, codom: Ob, fn_name: str) -> None:
        super().__init__(
            f"{Colors.FAIL} The image of {dom.name} under {fn_name} must be a subset of {codom.name} {Colors.ENDC}"
        )


def dom_is_subset_of_codom(
    name: str,
    dom: Ob,
    codom: Ob,
    fn: Callable,
) -> Optional[bool]:
    # Contract
    if all([fn(val) in codom.value for val in dom.value]):
        return True
    raise ImageIsNotSubsetOfCodom(dom, codom, name)


def type_of_dom_matches_type_of_codom(dom: Ob, codom: Ob) -> bool:
    # Contract
    return dom._type == codom._type


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
            f"The codomain of {f.name} was {f.codom.name}, while the domain of {g.name} was {g.dom.name}."
            f"{Colors.ENDC}"
        )


def homs_are_composable(f: Hom, g: Hom) -> Optional[bool]:
    # Contract
    if f.codom == g.dom:
        return True
    raise NotComposable(f, g)
