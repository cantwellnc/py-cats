from typing import Iterable


class Ob:
    def __init__(self, name: str, _type: type, value: Iterable) -> None:
        self.name = name
        self._type = _type
        self.value = value
