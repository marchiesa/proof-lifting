"""Parse Z3 S-expression proof output."""

from dataclasses import dataclass
from typing import Union, List, Optional


@dataclass
class Atom:
    """An atomic S-expression value (symbol, number, string)."""
    value: str

    def __repr__(self):
        return self.value


@dataclass
class SList:
    """A list S-expression."""
    items: List['SExpr']

    def __repr__(self):
        if len(self.items) <= 3:
            return f"({' '.join(repr(x) for x in self.items)})"
        return f"({repr(self.items[0])} ... {len(self.items)-1} more)"

    def __iter__(self):
        return iter(self.items)

    def __len__(self):
        return len(self.items)

    def __getitem__(self, key):
        return self.items[key]


SExpr = Union[Atom, SList]


class SExprParser:
    """Parse S-expressions from a string."""

    def __init__(self, text: str):
        self.text = text
        self.pos = 0
        self.length = len(text)

    def parse(self) -> Optional[SExpr]:
        """Parse a single S-expression."""
        self._skip_whitespace()
        if self.pos >= self.length:
            return None

        ch = self.text[self.pos]

        if ch == '(':
            return self._parse_list()
        elif ch == ')':
            raise ValueError(f"Unexpected ')' at position {self.pos}")
        elif ch == '"':
            return self._parse_string()
        elif ch == '|':
            return self._parse_quoted_symbol()
        else:
            return self._parse_atom()

    def parse_all(self) -> List[SExpr]:
        """Parse all S-expressions in the input."""
        result = []
        while True:
            expr = self.parse()
            if expr is None:
                break
            result.append(expr)
        return result

    def _skip_whitespace(self):
        """Skip whitespace and comments."""
        while self.pos < self.length:
            ch = self.text[self.pos]
            if ch in ' \t\n\r':
                self.pos += 1
            elif ch == ';':
                # Skip comment to end of line
                while self.pos < self.length and self.text[self.pos] != '\n':
                    self.pos += 1
            else:
                break

    def _parse_list(self) -> SList:
        """Parse a list: (item item ...)"""
        assert self.text[self.pos] == '('
        self.pos += 1

        items = []
        while True:
            self._skip_whitespace()
            if self.pos >= self.length:
                raise ValueError("Unexpected end of input in list")
            if self.text[self.pos] == ')':
                self.pos += 1
                return SList(items)
            item = self.parse()
            if item is not None:
                items.append(item)

    def _parse_atom(self) -> Atom:
        """Parse an atom (symbol or number)."""
        start = self.pos
        while self.pos < self.length:
            ch = self.text[self.pos]
            if ch in ' \t\n\r()";':
                break
            self.pos += 1

        value = self.text[start:self.pos]
        return Atom(value)

    def _parse_string(self) -> Atom:
        """Parse a quoted string."""
        assert self.text[self.pos] == '"'
        self.pos += 1
        start = self.pos

        while self.pos < self.length:
            ch = self.text[self.pos]
            if ch == '"':
                value = self.text[start:self.pos]
                self.pos += 1
                return Atom(f'"{value}"')
            elif ch == '\\':
                self.pos += 2  # Skip escaped char
            else:
                self.pos += 1

        raise ValueError("Unterminated string")

    def _parse_quoted_symbol(self) -> Atom:
        """Parse a |quoted symbol|."""
        assert self.text[self.pos] == '|'
        self.pos += 1
        start = self.pos

        while self.pos < self.length:
            if self.text[self.pos] == '|':
                value = self.text[start:self.pos]
                self.pos += 1
                return Atom(value)
            self.pos += 1

        raise ValueError("Unterminated quoted symbol")


def parse_sexpr(text: str) -> Optional[SExpr]:
    """Parse a single S-expression from text."""
    parser = SExprParser(text)
    return parser.parse()


def parse_all_sexprs(text: str) -> List[SExpr]:
    """Parse all S-expressions from text."""
    parser = SExprParser(text)
    return parser.parse_all()
