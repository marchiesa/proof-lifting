"""Dafny AST parser.

Parses Dafny source files into an AST with source location tracking.
"""

from dataclasses import dataclass, field
from typing import List, Optional, Dict, Any, Union
from enum import Enum, auto
import re


@dataclass
class SourceLoc:
    """Source location in a file."""
    line: int  # 1-indexed
    column: int  # 0-indexed
    end_line: Optional[int] = None
    end_column: Optional[int] = None

    def __repr__(self):
        if self.end_line:
            return f"{self.line}:{self.column}-{self.end_line}:{self.end_column}"
        return f"{self.line}:{self.column}"


class TokenType(Enum):
    # Keywords
    FUNCTION = auto()
    METHOD = auto()
    GHOST = auto()
    PREDICATE = auto()
    LEMMA = auto()
    CLASS = auto()
    MODULE = auto()
    IMPORT = auto()
    DATATYPE = auto()
    TYPE = auto()
    CONST = auto()
    VAR = auto()
    IF = auto()
    THEN = auto()
    ELSE = auto()
    WHILE = auto()
    FOR = auto()
    FORALL = auto()
    EXISTS = auto()
    MATCH = auto()
    CASE = auto()
    RETURN = auto()
    RETURNS = auto()
    REQUIRES = auto()
    ENSURES = auto()
    INVARIANT = auto()
    DECREASES = auto()
    MODIFIES = auto()
    READS = auto()
    ASSERT = auto()
    ASSUME = auto()
    EXPECT = auto()
    PRINT = auto()
    CALC = auto()

    # Literals and identifiers
    IDENT = auto()
    NUMBER = auto()
    STRING = auto()
    CHAR = auto()

    # Operators
    PLUS = auto()
    MINUS = auto()
    STAR = auto()
    SLASH = auto()
    PERCENT = auto()
    EQ = auto()
    NEQ = auto()
    LT = auto()
    GT = auto()
    LE = auto()
    GE = auto()
    AND = auto()
    OR = auto()
    NOT = auto()
    IMPLIES = auto()
    EXPLIES = auto()
    IFF = auto()
    ASSIGN = auto()
    DOTDOT = auto()

    # Delimiters
    LPAREN = auto()
    RPAREN = auto()
    LBRACE = auto()
    RBRACE = auto()
    LBRACKET = auto()
    RBRACKET = auto()
    COMMA = auto()
    SEMICOLON = auto()
    COLON = auto()
    COLONCOLON = auto()
    DOT = auto()
    PIPE = auto()

    # Special
    ARROW = auto()  # ->
    FAT_ARROW = auto()  # =>
    ATTRIBUTE = auto()  # {:...}

    EOF = auto()
    NEWLINE = auto()
    COMMENT = auto()


@dataclass
class Token:
    type: TokenType
    value: str
    loc: SourceLoc


class Lexer:
    """Tokenizer for Dafny source."""

    KEYWORDS = {
        'function': TokenType.FUNCTION,
        'method': TokenType.METHOD,
        'ghost': TokenType.GHOST,
        'predicate': TokenType.PREDICATE,
        'lemma': TokenType.LEMMA,
        'class': TokenType.CLASS,
        'module': TokenType.MODULE,
        'import': TokenType.IMPORT,
        'datatype': TokenType.DATATYPE,
        'type': TokenType.TYPE,
        'const': TokenType.CONST,
        'var': TokenType.VAR,
        'if': TokenType.IF,
        'then': TokenType.THEN,
        'else': TokenType.ELSE,
        'while': TokenType.WHILE,
        'for': TokenType.FOR,
        'forall': TokenType.FORALL,
        'exists': TokenType.EXISTS,
        'match': TokenType.MATCH,
        'case': TokenType.CASE,
        'return': TokenType.RETURN,
        'returns': TokenType.RETURNS,
        'requires': TokenType.REQUIRES,
        'ensures': TokenType.ENSURES,
        'invariant': TokenType.INVARIANT,
        'decreases': TokenType.DECREASES,
        'modifies': TokenType.MODIFIES,
        'reads': TokenType.READS,
        'assert': TokenType.ASSERT,
        'assume': TokenType.ASSUME,
        'expect': TokenType.EXPECT,
        'print': TokenType.PRINT,
        'calc': TokenType.CALC,
    }

    def __init__(self, source: str):
        self.source = source
        self.pos = 0
        self.line = 1
        self.column = 0
        self.tokens: List[Token] = []

    def current_loc(self) -> SourceLoc:
        return SourceLoc(self.line, self.column)

    def peek(self, offset: int = 0) -> str:
        pos = self.pos + offset
        if pos >= len(self.source):
            return ''
        return self.source[pos]

    def advance(self) -> str:
        ch = self.peek()
        self.pos += 1
        if ch == '\n':
            self.line += 1
            self.column = 0
        else:
            self.column += 1
        return ch

    def skip_whitespace(self):
        while self.peek() in ' \t\r':
            self.advance()

    def skip_line_comment(self):
        while self.peek() and self.peek() != '\n':
            self.advance()

    def skip_block_comment(self):
        # Skip /*
        self.advance()
        self.advance()
        depth = 1
        while depth > 0 and self.peek():
            if self.peek() == '/' and self.peek(1) == '*':
                depth += 1
                self.advance()
                self.advance()
            elif self.peek() == '*' and self.peek(1) == '/':
                depth -= 1
                self.advance()
                self.advance()
            else:
                self.advance()

    def read_string(self, quote: str) -> str:
        result = quote
        self.advance()  # skip opening quote
        while self.peek() and self.peek() != quote:
            if self.peek() == '\\':
                result += self.advance()
            result += self.advance()
        if self.peek() == quote:
            result += self.advance()
        return result

    def read_number(self) -> str:
        result = ''
        while self.peek().isdigit() or self.peek() == '_':
            result += self.advance()
        # Handle decimal
        if self.peek() == '.' and self.peek(1).isdigit():
            result += self.advance()
            while self.peek().isdigit() or self.peek() == '_':
                result += self.advance()
        return result

    def read_ident(self) -> str:
        result = ''
        while self.peek().isalnum() or self.peek() in '_?\'':
            result += self.advance()
        return result

    def read_attribute(self) -> str:
        # {:name ...}
        result = ''
        depth = 1
        result += self.advance()  # {
        result += self.advance()  # :
        while depth > 0 and self.peek():
            ch = self.advance()
            result += ch
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
        return result

    def tokenize(self) -> List[Token]:
        self.tokens = []

        while self.pos < len(self.source):
            self.skip_whitespace()

            if not self.peek():
                break

            loc = self.current_loc()
            ch = self.peek()

            # Newline
            if ch == '\n':
                self.advance()
                self.tokens.append(Token(TokenType.NEWLINE, '\n', loc))
                continue

            # Comments
            if ch == '/' and self.peek(1) == '/':
                self.skip_line_comment()
                continue
            if ch == '/' and self.peek(1) == '*':
                self.skip_block_comment()
                continue

            # Attribute
            if ch == '{' and self.peek(1) == ':':
                value = self.read_attribute()
                self.tokens.append(Token(TokenType.ATTRIBUTE, value, loc))
                continue

            # String
            if ch == '"':
                value = self.read_string('"')
                self.tokens.append(Token(TokenType.STRING, value, loc))
                continue

            # Char
            if ch == "'":
                value = self.read_string("'")
                self.tokens.append(Token(TokenType.CHAR, value, loc))
                continue

            # Number
            if ch.isdigit():
                value = self.read_number()
                self.tokens.append(Token(TokenType.NUMBER, value, loc))
                continue

            # Identifier or keyword
            if ch.isalpha() or ch == '_':
                value = self.read_ident()
                ttype = self.KEYWORDS.get(value, TokenType.IDENT)
                self.tokens.append(Token(ttype, value, loc))
                continue

            # Two-character operators
            two_char = ch + self.peek(1)
            if two_char == '::':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.COLONCOLON, '::', loc))
                continue
            if two_char == '..':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.DOTDOT, '..', loc))
                continue
            if two_char == '->':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.ARROW, '->', loc))
                continue
            if two_char == '=>':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.FAT_ARROW, '=>', loc))
                continue
            if two_char == '==':
                three_char = two_char + self.peek(2)
                if three_char == '==>':
                    self.advance(); self.advance(); self.advance()
                    self.tokens.append(Token(TokenType.IMPLIES, '==>', loc))
                    continue
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.EQ, '==', loc))
                continue
            if two_char == '!=':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.NEQ, '!=', loc))
                continue
            if two_char == '<=':
                three_char = two_char + self.peek(2)
                # Check for <==> (4 chars) BEFORE <== (3 chars)
                if three_char == '<==' and self.peek(3) == '>':
                    self.advance(); self.advance(); self.advance(); self.advance()
                    self.tokens.append(Token(TokenType.IFF, '<==>', loc))
                    continue
                if three_char == '<==':
                    self.advance(); self.advance(); self.advance()
                    self.tokens.append(Token(TokenType.EXPLIES, '<==', loc))
                    continue
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.LE, '<=', loc))
                continue
            if two_char == '>=':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.GE, '>=', loc))
                continue
            if two_char == '&&':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.AND, '&&', loc))
                continue
            if two_char == '||':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.OR, '||', loc))
                continue
            if two_char == ':=':
                self.advance(); self.advance()
                self.tokens.append(Token(TokenType.ASSIGN, ':=', loc))
                continue

            # Single-character tokens
            single_char_tokens = {
                '(': TokenType.LPAREN,
                ')': TokenType.RPAREN,
                '{': TokenType.LBRACE,
                '}': TokenType.RBRACE,
                '[': TokenType.LBRACKET,
                ']': TokenType.RBRACKET,
                ',': TokenType.COMMA,
                ';': TokenType.SEMICOLON,
                ':': TokenType.COLON,
                '.': TokenType.DOT,
                '|': TokenType.PIPE,
                '+': TokenType.PLUS,
                '-': TokenType.MINUS,
                '*': TokenType.STAR,
                '/': TokenType.SLASH,
                '%': TokenType.PERCENT,
                '<': TokenType.LT,
                '>': TokenType.GT,
                '!': TokenType.NOT,
                '=': TokenType.ASSIGN,  # Single = is assignment in some contexts
            }

            if ch in single_char_tokens:
                self.advance()
                self.tokens.append(Token(single_char_tokens[ch], ch, loc))
                continue

            # Unknown character - skip
            self.advance()

        self.tokens.append(Token(TokenType.EOF, '', self.current_loc()))
        return self.tokens


# AST Node types

@dataclass
class ASTNode:
    """Base class for AST nodes."""
    loc: SourceLoc


@dataclass
class Expr(ASTNode):
    """Base class for expressions."""
    pass


@dataclass
class IdentExpr(Expr):
    name: str


@dataclass
class NumberExpr(Expr):
    value: str


@dataclass
class StringExpr(Expr):
    value: str


@dataclass
class BinaryExpr(Expr):
    op: str
    left: Expr
    right: Expr


@dataclass
class UnaryExpr(Expr):
    op: str
    operand: Expr


@dataclass
class CallExpr(Expr):
    func: Expr
    args: List[Expr]


@dataclass
class IndexExpr(Expr):
    base: Expr
    index: Expr


@dataclass
class SliceExpr(Expr):
    base: Expr
    start: Optional[Expr]
    end: Optional[Expr]


@dataclass
class LengthExpr(Expr):
    """Sequence length |s|"""
    operand: Expr


@dataclass
class IfExpr(Expr):
    condition: Expr
    then_expr: Expr
    else_expr: Expr


@dataclass
class QuantifierExpr(Expr):
    kind: str  # 'forall' or 'exists'
    vars: List[tuple]  # [(name, type), ...]
    body: Expr


@dataclass
class ParenExpr(Expr):
    inner: Expr


# Statement types

@dataclass
class Stmt(ASTNode):
    """Base class for statements."""
    pass


@dataclass
class VarDeclStmt(Stmt):
    name: str
    type_: Optional[str]
    init: Optional[Expr]


@dataclass
class AssignStmt(Stmt):
    targets: List[Expr]
    values: List[Expr]


@dataclass
class IfStmt(Stmt):
    condition: Expr
    then_block: List[Stmt]
    else_block: Optional[List[Stmt]]


@dataclass
class WhileStmt(Stmt):
    condition: Expr
    invariants: List[Expr]
    decreases: List[Expr]
    modifies: List[Expr]
    body: List[Stmt]


@dataclass
class AssertStmt(Stmt):
    expr: Expr
    label: Optional[str] = None


@dataclass
class AssumeStmt(Stmt):
    expr: Expr


@dataclass
class ReturnStmt(Stmt):
    values: List[Expr]


@dataclass
class CalcStmt(Stmt):
    """Calc block statement."""
    steps: List[tuple]  # [(expr, hint), ...]


@dataclass
class BlockStmt(Stmt):
    stmts: List[Stmt]


# Top-level declarations

@dataclass
class Parameter:
    name: str
    type_: str
    loc: SourceLoc


@dataclass
class FunctionDecl(ASTNode):
    name: str
    params: List[Parameter]
    return_type: str
    body: Optional[Expr]
    requires: List[Expr] = field(default_factory=list)
    ensures: List[Expr] = field(default_factory=list)
    decreases: List[Expr] = field(default_factory=list)
    is_ghost: bool = False


@dataclass
class MethodDecl(ASTNode):
    name: str
    params: List[Parameter]
    returns: List[Parameter]
    body: Optional[List[Stmt]]
    requires: List[Expr] = field(default_factory=list)
    ensures: List[Expr] = field(default_factory=list)
    decreases: List[Expr] = field(default_factory=list)
    modifies: List[Expr] = field(default_factory=list)


@dataclass
class DafnyFile(ASTNode):
    """Root AST node for a Dafny file."""
    path: str
    functions: List[FunctionDecl] = field(default_factory=list)
    methods: List[MethodDecl] = field(default_factory=list)


class Parser:
    """Parser for Dafny source."""

    def __init__(self, tokens: List[Token]):
        self.tokens = [t for t in tokens if t.type != TokenType.NEWLINE]
        self.pos = 0

    def current(self) -> Token:
        if self.pos >= len(self.tokens):
            return self.tokens[-1]  # EOF
        return self.tokens[self.pos]

    def peek(self, offset: int = 0) -> Token:
        pos = self.pos + offset
        if pos >= len(self.tokens):
            return self.tokens[-1]
        return self.tokens[pos]

    def advance(self) -> Token:
        tok = self.current()
        self.pos += 1
        return tok

    def expect(self, ttype: TokenType) -> Token:
        if self.current().type != ttype:
            raise SyntaxError(f"Expected {ttype}, got {self.current().type} at {self.current().loc}")
        return self.advance()

    def match(self, *types: TokenType) -> bool:
        return self.current().type in types

    def parse_file(self, path: str = "") -> DafnyFile:
        """Parse a complete Dafny file."""
        loc = self.current().loc
        file = DafnyFile(loc=loc, path=path)

        while not self.match(TokenType.EOF):
            if self.match(TokenType.FUNCTION, TokenType.GHOST):
                func = self.parse_function()
                file.functions.append(func)
            elif self.match(TokenType.METHOD, TokenType.LEMMA):
                method = self.parse_method()
                file.methods.append(method)
            elif self.match(TokenType.PREDICATE):
                # Predicate is like a function returning bool
                func = self.parse_function()
                file.functions.append(func)
            else:
                # Skip unknown top-level items
                self.advance()

        return file

    def parse_function(self) -> FunctionDecl:
        """Parse a function declaration."""
        loc = self.current().loc
        is_ghost = False

        if self.match(TokenType.GHOST):
            is_ghost = True
            self.advance()

        if self.match(TokenType.PREDICATE):
            self.advance()
            return_type = "bool"
        else:
            self.expect(TokenType.FUNCTION)
            return_type = None

        name = self.expect(TokenType.IDENT).value

        # Parameters
        self.expect(TokenType.LPAREN)
        params = self.parse_parameters()
        self.expect(TokenType.RPAREN)

        # Return type (if not predicate)
        if return_type is None:
            self.expect(TokenType.COLON)
            return_type = self.parse_type()

        # Specifications
        requires = []
        ensures = []
        decreases = []

        while self.match(TokenType.REQUIRES, TokenType.ENSURES, TokenType.DECREASES, TokenType.READS):
            if self.match(TokenType.REQUIRES):
                self.advance()
                requires.append(self.parse_expr())
            elif self.match(TokenType.ENSURES):
                self.advance()
                ensures.append(self.parse_expr())
            elif self.match(TokenType.DECREASES):
                self.advance()
                decreases.append(self.parse_expr())
            elif self.match(TokenType.READS):
                self.advance()
                self.parse_expr()  # Skip reads clause

        # Body
        body = None
        if self.match(TokenType.LBRACE):
            self.expect(TokenType.LBRACE)
            body = self.parse_expr()
            self.expect(TokenType.RBRACE)

        return FunctionDecl(
            loc=loc,
            name=name,
            params=params,
            return_type=return_type,
            body=body,
            requires=requires,
            ensures=ensures,
            decreases=decreases,
            is_ghost=is_ghost
        )

    def parse_method(self) -> MethodDecl:
        """Parse a method declaration."""
        loc = self.current().loc

        if self.match(TokenType.LEMMA):
            self.advance()
        else:
            self.expect(TokenType.METHOD)

        name = self.expect(TokenType.IDENT).value

        # Parameters
        self.expect(TokenType.LPAREN)
        params = self.parse_parameters()
        self.expect(TokenType.RPAREN)

        # Returns
        returns = []
        if self.match(TokenType.RETURNS):
            self.advance()
            self.expect(TokenType.LPAREN)
            returns = self.parse_parameters()
            self.expect(TokenType.RPAREN)

        # Specifications
        requires = []
        ensures = []
        decreases = []
        modifies = []

        while self.match(TokenType.REQUIRES, TokenType.ENSURES, TokenType.DECREASES, TokenType.MODIFIES):
            if self.match(TokenType.REQUIRES):
                self.advance()
                requires.append(self.parse_expr())
            elif self.match(TokenType.ENSURES):
                self.advance()
                ensures.append(self.parse_expr())
            elif self.match(TokenType.DECREASES):
                self.advance()
                decreases.append(self.parse_expr())
            elif self.match(TokenType.MODIFIES):
                self.advance()
                modifies.append(self.parse_expr())

        # Body
        body = None
        if self.match(TokenType.LBRACE):
            body = self.parse_block()

        return MethodDecl(
            loc=loc,
            name=name,
            params=params,
            returns=returns,
            body=body,
            requires=requires,
            ensures=ensures,
            decreases=decreases,
            modifies=modifies
        )

    def parse_parameters(self) -> List[Parameter]:
        """Parse parameter list."""
        params = []

        while not self.match(TokenType.RPAREN):
            loc = self.current().loc
            name = self.expect(TokenType.IDENT).value
            self.expect(TokenType.COLON)
            type_ = self.parse_type()
            params.append(Parameter(name=name, type_=type_, loc=loc))

            if self.match(TokenType.COMMA):
                self.advance()

        return params

    def parse_type(self) -> str:
        """Parse a type expression (simplified - just returns string)."""
        result = ""
        depth = 0

        while True:
            if self.match(TokenType.RPAREN, TokenType.COMMA) and depth == 0:
                break
            if self.match(TokenType.LBRACE, TokenType.REQUIRES, TokenType.ENSURES,
                         TokenType.DECREASES, TokenType.MODIFIES, TokenType.READS):
                break
            if self.match(TokenType.EOF):
                break

            tok = self.advance()
            if tok.type == TokenType.LT:
                depth += 1
            elif tok.type == TokenType.GT:
                depth -= 1
            result += tok.value

        return result.strip()

    def parse_block(self) -> List[Stmt]:
        """Parse a statement block."""
        self.expect(TokenType.LBRACE)
        stmts = []

        while not self.match(TokenType.RBRACE, TokenType.EOF):
            stmt = self.parse_stmt()
            if stmt:
                stmts.append(stmt)

        self.expect(TokenType.RBRACE)
        return stmts

    def parse_stmt(self) -> Optional[Stmt]:
        """Parse a statement."""
        loc = self.current().loc

        if self.match(TokenType.VAR):
            return self.parse_var_decl()
        elif self.match(TokenType.IF):
            return self.parse_if_stmt()
        elif self.match(TokenType.WHILE):
            return self.parse_while_stmt()
        elif self.match(TokenType.ASSERT):
            return self.parse_assert_stmt()
        elif self.match(TokenType.ASSUME):
            self.advance()
            expr = self.parse_expr()
            self.expect(TokenType.SEMICOLON)
            return AssumeStmt(loc=loc, expr=expr)
        elif self.match(TokenType.RETURN):
            self.advance()
            values = []
            if not self.match(TokenType.SEMICOLON):
                values.append(self.parse_expr())
                while self.match(TokenType.COMMA):
                    self.advance()
                    values.append(self.parse_expr())
            self.expect(TokenType.SEMICOLON)
            return ReturnStmt(loc=loc, values=values)
        elif self.match(TokenType.CALC):
            return self.parse_calc_stmt()
        elif self.match(TokenType.LBRACE):
            stmts = self.parse_block()
            return BlockStmt(loc=loc, stmts=stmts)
        elif self.match(TokenType.IDENT):
            # Could be assignment or call
            return self.parse_assign_or_call()
        else:
            # Skip unknown statement
            self.advance()
            return None

    def parse_var_decl(self) -> VarDeclStmt:
        """Parse variable declaration."""
        loc = self.current().loc
        self.expect(TokenType.VAR)
        name = self.expect(TokenType.IDENT).value

        type_ = None
        if self.match(TokenType.COLON):
            self.advance()
            type_ = self.parse_type()

        init = None
        if self.match(TokenType.ASSIGN):
            self.advance()
            init = self.parse_expr()

        self.expect(TokenType.SEMICOLON)
        return VarDeclStmt(loc=loc, name=name, type_=type_, init=init)

    def parse_if_stmt(self) -> IfStmt:
        """Parse if statement."""
        loc = self.current().loc
        self.expect(TokenType.IF)
        condition = self.parse_expr()
        then_block = self.parse_block()

        else_block = None
        if self.match(TokenType.ELSE):
            self.advance()
            if self.match(TokenType.IF):
                else_block = [self.parse_if_stmt()]
            else:
                else_block = self.parse_block()

        return IfStmt(loc=loc, condition=condition, then_block=then_block, else_block=else_block)

    def parse_while_stmt(self) -> WhileStmt:
        """Parse while statement."""
        loc = self.current().loc
        self.expect(TokenType.WHILE)
        condition = self.parse_expr()

        invariants = []
        decreases = []
        modifies = []

        while self.match(TokenType.INVARIANT, TokenType.DECREASES, TokenType.MODIFIES):
            if self.match(TokenType.INVARIANT):
                self.advance()
                invariants.append(self.parse_expr())
            elif self.match(TokenType.DECREASES):
                self.advance()
                decreases.append(self.parse_expr())
            elif self.match(TokenType.MODIFIES):
                self.advance()
                modifies.append(self.parse_expr())

        body = self.parse_block()

        return WhileStmt(
            loc=loc,
            condition=condition,
            invariants=invariants,
            decreases=decreases,
            modifies=modifies,
            body=body
        )

    def parse_assert_stmt(self) -> AssertStmt:
        """Parse assert statement."""
        loc = self.current().loc
        self.expect(TokenType.ASSERT)

        # Check for label
        label = None
        # Skip attribute if present
        if self.match(TokenType.ATTRIBUTE):
            self.advance()

        expr = self.parse_expr()

        # Handle "by { ... }" clause
        if self.match(TokenType.IDENT) and self.current().value == "by":
            self.advance()
            self.parse_block()  # Skip the by block for now

        self.expect(TokenType.SEMICOLON)
        return AssertStmt(loc=loc, expr=expr, label=label)

    def parse_calc_stmt(self) -> CalcStmt:
        """Parse calc statement."""
        loc = self.current().loc
        self.expect(TokenType.CALC)

        # Skip calc body for now - just match braces
        self.expect(TokenType.LBRACE)
        depth = 1
        while depth > 0:
            if self.match(TokenType.LBRACE):
                depth += 1
            elif self.match(TokenType.RBRACE):
                depth -= 1
            if depth > 0:
                self.advance()
        self.expect(TokenType.RBRACE)

        return CalcStmt(loc=loc, steps=[])

    def parse_assign_or_call(self) -> Stmt:
        """Parse assignment or call statement."""
        loc = self.current().loc

        # Parse left-hand side(s)
        targets = [self.parse_expr()]
        while self.match(TokenType.COMMA):
            self.advance()
            targets.append(self.parse_expr())

        if self.match(TokenType.ASSIGN):
            self.advance()
            values = [self.parse_expr()]
            while self.match(TokenType.COMMA):
                self.advance()
                values.append(self.parse_expr())
            self.expect(TokenType.SEMICOLON)
            return AssignStmt(loc=loc, targets=targets, values=values)
        else:
            # Just an expression statement (call)
            self.expect(TokenType.SEMICOLON)
            return AssignStmt(loc=loc, targets=[], values=targets)

    def parse_expr(self) -> Expr:
        """Parse an expression."""
        return self.parse_implies_expr()

    def parse_implies_expr(self) -> Expr:
        """Parse implication expressions."""
        left = self.parse_or_expr()

        while self.match(TokenType.IMPLIES, TokenType.EXPLIES, TokenType.IFF):
            op = self.advance().value
            right = self.parse_or_expr()
            left = BinaryExpr(loc=left.loc, op=op, left=left, right=right)

        return left

    def parse_or_expr(self) -> Expr:
        left = self.parse_and_expr()

        while self.match(TokenType.OR):
            op = self.advance().value
            right = self.parse_and_expr()
            left = BinaryExpr(loc=left.loc, op=op, left=left, right=right)

        return left

    def parse_and_expr(self) -> Expr:
        left = self.parse_comparison_expr()

        while self.match(TokenType.AND):
            op = self.advance().value
            right = self.parse_comparison_expr()
            left = BinaryExpr(loc=left.loc, op=op, left=left, right=right)

        return left

    def parse_comparison_expr(self) -> Expr:
        left = self.parse_additive_expr()

        while self.match(TokenType.EQ, TokenType.NEQ, TokenType.LT, TokenType.GT,
                        TokenType.LE, TokenType.GE):
            op = self.advance().value
            right = self.parse_additive_expr()
            left = BinaryExpr(loc=left.loc, op=op, left=left, right=right)

        return left

    def parse_additive_expr(self) -> Expr:
        left = self.parse_multiplicative_expr()

        while self.match(TokenType.PLUS, TokenType.MINUS):
            op = self.advance().value
            right = self.parse_multiplicative_expr()
            left = BinaryExpr(loc=left.loc, op=op, left=left, right=right)

        return left

    def parse_multiplicative_expr(self) -> Expr:
        left = self.parse_unary_expr()

        while self.match(TokenType.STAR, TokenType.SLASH, TokenType.PERCENT):
            op = self.advance().value
            right = self.parse_unary_expr()
            left = BinaryExpr(loc=left.loc, op=op, left=left, right=right)

        return left

    def parse_unary_expr(self) -> Expr:
        if self.match(TokenType.NOT, TokenType.MINUS):
            loc = self.current().loc
            op = self.advance().value
            operand = self.parse_unary_expr()
            return UnaryExpr(loc=loc, op=op, operand=operand)

        return self.parse_postfix_expr()

    def parse_postfix_expr(self) -> Expr:
        expr = self.parse_primary_expr()

        while True:
            if self.match(TokenType.LPAREN):
                # Function call
                self.advance()
                args = []
                if not self.match(TokenType.RPAREN):
                    args.append(self.parse_expr())
                    while self.match(TokenType.COMMA):
                        self.advance()
                        args.append(self.parse_expr())
                self.expect(TokenType.RPAREN)
                expr = CallExpr(loc=expr.loc, func=expr, args=args)
            elif self.match(TokenType.LBRACKET):
                # Index or slice
                self.advance()
                if self.match(TokenType.DOTDOT):
                    # Slice from start: s[..end]
                    self.advance()
                    end = self.parse_expr()
                    self.expect(TokenType.RBRACKET)
                    expr = SliceExpr(loc=expr.loc, base=expr, start=None, end=end)
                else:
                    index = self.parse_expr()
                    if self.match(TokenType.DOTDOT):
                        # Slice: s[start..end] or s[start..]
                        self.advance()
                        end = None
                        if not self.match(TokenType.RBRACKET):
                            end = self.parse_expr()
                        self.expect(TokenType.RBRACKET)
                        expr = SliceExpr(loc=expr.loc, base=expr, start=index, end=end)
                    else:
                        # Simple index
                        self.expect(TokenType.RBRACKET)
                        expr = IndexExpr(loc=expr.loc, base=expr, index=index)
            elif self.match(TokenType.DOT):
                # Field access
                self.advance()
                if self.match(TokenType.IDENT):
                    field = self.advance().value
                    expr = BinaryExpr(loc=expr.loc, op='.', left=expr,
                                     right=IdentExpr(loc=expr.loc, name=field))
                else:
                    break
            else:
                break

        return expr

    def parse_primary_expr(self) -> Expr:
        loc = self.current().loc

        if self.match(TokenType.NUMBER):
            return NumberExpr(loc=loc, value=self.advance().value)

        if self.match(TokenType.STRING):
            return StringExpr(loc=loc, value=self.advance().value)

        if self.match(TokenType.IDENT):
            return IdentExpr(loc=loc, name=self.advance().value)

        if self.match(TokenType.LPAREN):
            self.advance()
            expr = self.parse_expr()
            self.expect(TokenType.RPAREN)
            return ParenExpr(loc=loc, inner=expr)

        if self.match(TokenType.PIPE):
            # Sequence length |s|
            self.advance()
            operand = self.parse_expr()
            self.expect(TokenType.PIPE)
            return LengthExpr(loc=loc, operand=operand)

        if self.match(TokenType.IF):
            return self.parse_if_expr()

        if self.match(TokenType.FORALL, TokenType.EXISTS):
            return self.parse_quantifier_expr()

        # Unknown - return dummy
        return IdentExpr(loc=loc, name=self.advance().value)

    def parse_if_expr(self) -> IfExpr:
        """Parse if-then-else expression."""
        loc = self.current().loc
        self.expect(TokenType.IF)
        condition = self.parse_expr()
        self.expect(TokenType.THEN)
        then_expr = self.parse_expr()
        self.expect(TokenType.ELSE)
        else_expr = self.parse_expr()
        return IfExpr(loc=loc, condition=condition, then_expr=then_expr, else_expr=else_expr)

    def parse_quantifier_expr(self) -> QuantifierExpr:
        """Parse forall/exists expression."""
        loc = self.current().loc
        kind = 'forall' if self.match(TokenType.FORALL) else 'exists'
        self.advance()

        # Parse bound variables
        vars = []
        name = self.expect(TokenType.IDENT).value
        type_ = None
        if self.match(TokenType.COLON):
            self.advance()
            type_ = self.parse_type()
        vars.append((name, type_))

        while self.match(TokenType.COMMA):
            self.advance()
            name = self.expect(TokenType.IDENT).value
            type_ = None
            if self.match(TokenType.COLON):
                self.advance()
                type_ = self.parse_type()
            vars.append((name, type_))

        self.expect(TokenType.COLONCOLON)
        body = self.parse_expr()

        return QuantifierExpr(loc=loc, kind=kind, vars=vars, body=body)


def parse_dafny_file(source: str, path: str = "") -> DafnyFile:
    """Parse a Dafny source file into an AST."""
    lexer = Lexer(source)
    tokens = lexer.tokenize()
    parser = Parser(tokens)
    return parser.parse_file(path)


def expr_to_string(expr: Expr) -> str:
    """Convert an expression AST back to string form."""
    if isinstance(expr, IdentExpr):
        return expr.name
    elif isinstance(expr, NumberExpr):
        return expr.value
    elif isinstance(expr, StringExpr):
        return expr.value
    elif isinstance(expr, BinaryExpr):
        left = expr_to_string(expr.left)
        right = expr_to_string(expr.right)
        if expr.op == '.':
            return f"{left}.{right}"
        return f"{left} {expr.op} {right}"
    elif isinstance(expr, UnaryExpr):
        operand = expr_to_string(expr.operand)
        if expr.op == '!':
            return f"!{operand}"
        return f"{expr.op}{operand}"
    elif isinstance(expr, CallExpr):
        func = expr_to_string(expr.func)
        args = ", ".join(expr_to_string(a) for a in expr.args)
        return f"{func}({args})"
    elif isinstance(expr, IndexExpr):
        base = expr_to_string(expr.base)
        index = expr_to_string(expr.index)
        return f"{base}[{index}]"
    elif isinstance(expr, SliceExpr):
        base = expr_to_string(expr.base)
        start = expr_to_string(expr.start) if expr.start else ""
        end = expr_to_string(expr.end) if expr.end else ""
        return f"{base}[{start}..{end}]"
    elif isinstance(expr, LengthExpr):
        operand = expr_to_string(expr.operand)
        return f"|{operand}|"
    elif isinstance(expr, IfExpr):
        cond = expr_to_string(expr.condition)
        then_e = expr_to_string(expr.then_expr)
        else_e = expr_to_string(expr.else_expr)
        return f"if {cond} then {then_e} else {else_e}"
    elif isinstance(expr, ParenExpr):
        return f"({expr_to_string(expr.inner)})"
    elif isinstance(expr, QuantifierExpr):
        vars_str = ", ".join(f"{n}: {t}" if t else n for n, t in expr.vars)
        body = expr_to_string(expr.body)
        return f"{expr.kind} {vars_str} :: {body}"
    else:
        return str(expr)


def substitute_expr(expr: Expr, bindings: Dict[str, Expr]) -> Expr:
    """Substitute variables in an expression according to bindings."""

    if isinstance(expr, IdentExpr):
        if expr.name in bindings:
            return bindings[expr.name]
        return expr
    elif isinstance(expr, NumberExpr):
        return expr
    elif isinstance(expr, StringExpr):
        return expr
    elif isinstance(expr, BinaryExpr):
        return BinaryExpr(
            loc=expr.loc, op=expr.op,
            left=substitute_expr(expr.left, bindings),
            right=substitute_expr(expr.right, bindings)
        )
    elif isinstance(expr, UnaryExpr):
        return UnaryExpr(
            loc=expr.loc, op=expr.op,
            operand=substitute_expr(expr.operand, bindings)
        )
    elif isinstance(expr, CallExpr):
        return CallExpr(
            loc=expr.loc,
            func=substitute_expr(expr.func, bindings),
            args=[substitute_expr(a, bindings) for a in expr.args]
        )
    elif isinstance(expr, IndexExpr):
        return IndexExpr(
            loc=expr.loc,
            base=substitute_expr(expr.base, bindings),
            index=substitute_expr(expr.index, bindings)
        )
    elif isinstance(expr, SliceExpr):
        return SliceExpr(
            loc=expr.loc,
            base=substitute_expr(expr.base, bindings),
            start=substitute_expr(expr.start, bindings) if expr.start else None,
            end=substitute_expr(expr.end, bindings) if expr.end else None
        )
    elif isinstance(expr, LengthExpr):
        return LengthExpr(
            loc=expr.loc,
            operand=substitute_expr(expr.operand, bindings)
        )
    elif isinstance(expr, IfExpr):
        return IfExpr(
            loc=expr.loc,
            condition=substitute_expr(expr.condition, bindings),
            then_expr=substitute_expr(expr.then_expr, bindings),
            else_expr=substitute_expr(expr.else_expr, bindings)
        )
    elif isinstance(expr, ParenExpr):
        return ParenExpr(
            loc=expr.loc,
            inner=substitute_expr(expr.inner, bindings)
        )
    return expr


def simplify_expr(expr: Expr) -> Expr:
    """Simplify an expression using algebraic rules."""

    # First, recursively simplify sub-expressions
    if isinstance(expr, BinaryExpr):
        left = simplify_expr(expr.left)
        right = simplify_expr(expr.right)
        expr = BinaryExpr(loc=expr.loc, op=expr.op, left=left, right=right)

        # Simplify: (a + b) - b -> a
        if expr.op == '-' and isinstance(right, NumberExpr):
            if isinstance(left, BinaryExpr) and left.op == '+':
                if isinstance(left.right, NumberExpr) and left.right.value == right.value:
                    return left.left

        # Simplify: a + 0 -> a, a - 0 -> a
        if expr.op in ('+', '-') and isinstance(right, NumberExpr) and right.value == '0':
            return left

    elif isinstance(expr, UnaryExpr):
        operand = simplify_expr(expr.operand)
        expr = UnaryExpr(loc=expr.loc, op=expr.op, operand=operand)

    elif isinstance(expr, CallExpr):
        func = simplify_expr(expr.func)
        args = [simplify_expr(a) for a in expr.args]
        expr = CallExpr(loc=expr.loc, func=func, args=args)

    elif isinstance(expr, IndexExpr):
        base = simplify_expr(expr.base)
        index = simplify_expr(expr.index)
        expr = IndexExpr(loc=expr.loc, base=base, index=index)

        # Simplify: s[..n][m] -> s[m]
        if isinstance(base, SliceExpr) and base.start is None:
            return IndexExpr(loc=expr.loc, base=base.base, index=index)

    elif isinstance(expr, SliceExpr):
        base = simplify_expr(expr.base)
        start = simplify_expr(expr.start) if expr.start else None
        end = simplify_expr(expr.end) if expr.end else None
        expr = SliceExpr(loc=expr.loc, base=base, start=start, end=end)

        # Simplify: s[..n][..m] -> s[..m]
        if isinstance(base, SliceExpr) and base.start is None and start is None:
            return SliceExpr(loc=expr.loc, base=base.base, start=None, end=end)

    elif isinstance(expr, LengthExpr):
        operand = simplify_expr(expr.operand)
        expr = LengthExpr(loc=expr.loc, operand=operand)

        # Simplify: |s[..n]| -> n
        if isinstance(operand, SliceExpr) and operand.start is None and operand.end:
            return operand.end

    elif isinstance(expr, ParenExpr):
        inner = simplify_expr(expr.inner)
        # Remove unnecessary parens around simple expressions
        if isinstance(inner, (IdentExpr, NumberExpr)):
            return inner
        expr = ParenExpr(loc=expr.loc, inner=inner)

    return expr


def generate_unfolding_calc(func: FunctionDecl, arg_exprs: List[Expr],
                            indent: str = "    ") -> Optional[str]:
    """Generate a calc block for unfolding a function with given arguments.

    Works for any function with if-then-else body.
    Returns None if function doesn't have appropriate structure.
    """
    if not func.body or not isinstance(func.body, IfExpr):
        return None

    # Create bindings from params to args
    bindings = {}
    for param, arg in zip(func.params, arg_exprs):
        bindings[param.name] = arg

    # The function call
    call = CallExpr(
        loc=func.loc,
        func=IdentExpr(loc=func.loc, name=func.name),
        args=arg_exprs
    )

    # Substitute and simplify the recursive case (else branch)
    recursive_case = substitute_expr(func.body.else_expr, bindings)
    recursive_case = simplify_expr(recursive_case)

    lines = [
        f'{indent}calc {{',
        f'{indent}    {expr_to_string(call)};',
        f'{indent}    ==  // unfold {func.name} definition',
        f'{indent}    {expr_to_string(recursive_case)};',
        f'{indent}}}'
    ]

    return '\n'.join(lines)


def increment_expr(expr: Expr) -> Expr:
    """Create expr + 1."""
    return BinaryExpr(
        loc=expr.loc,
        op='+',
        left=expr,
        right=NumberExpr(loc=expr.loc, value=1)
    )


def find_slice_in_expr(expr: Expr) -> Optional[SliceExpr]:
    """Find the first slice expression in an expression (e.g., s[..i] in Sum(s[..i]))."""
    if isinstance(expr, SliceExpr):
        return expr
    elif isinstance(expr, CallExpr):
        for arg in expr.args:
            result = find_slice_in_expr(arg)
            if result:
                return result
    elif isinstance(expr, BinaryExpr):
        result = find_slice_in_expr(expr.left)
        if result:
            return result
        return find_slice_in_expr(expr.right)
    elif isinstance(expr, IndexExpr):
        result = find_slice_in_expr(expr.base)
        if result:
            return result
        return find_slice_in_expr(expr.index)
    elif isinstance(expr, ParenExpr):
        return find_slice_in_expr(expr.inner)
    elif isinstance(expr, LengthExpr):
        return find_slice_in_expr(expr.operand)
    return None


def replace_slice_end(expr: Expr, old_end: Expr, new_end: Expr) -> Expr:
    """Replace the end of a slice expression throughout an expression tree."""
    if isinstance(expr, SliceExpr):
        if expr.end and expr_to_string(expr.end) == expr_to_string(old_end):
            return SliceExpr(loc=expr.loc, base=expr.base, start=expr.start, end=new_end)
        return expr
    elif isinstance(expr, CallExpr):
        new_args = [replace_slice_end(arg, old_end, new_end) for arg in expr.args]
        return CallExpr(loc=expr.loc, func=expr.func, args=new_args)
    elif isinstance(expr, BinaryExpr):
        return BinaryExpr(
            loc=expr.loc,
            op=expr.op,
            left=replace_slice_end(expr.left, old_end, new_end),
            right=replace_slice_end(expr.right, old_end, new_end)
        )
    elif isinstance(expr, IndexExpr):
        return IndexExpr(
            loc=expr.loc,
            base=replace_slice_end(expr.base, old_end, new_end),
            index=replace_slice_end(expr.index, old_end, new_end)
        )
    elif isinstance(expr, ParenExpr):
        return ParenExpr(loc=expr.loc, inner=replace_slice_end(expr.inner, old_end, new_end))
    elif isinstance(expr, LengthExpr):
        return LengthExpr(loc=expr.loc, operand=replace_slice_end(expr.operand, old_end, new_end))
    return expr


def generate_folding_calc(func: FunctionDecl, arg_exprs: List[Expr],
                          indent: str = "    ") -> Optional[str]:
    """Generate a calc block for folding a function call (for loop invariant maintenance).

    Given a call like Sum(s[..i]), generates:
        calc {
            Sum(s[..i]) + s[i];
            == { fold Sum definition }
            Sum(s[..i+1]);
        }

    This is the reverse of unfolding, useful for proving loop invariant maintenance.
    """
    if not func.body or not isinstance(func.body, IfExpr):
        return None

    # Find the first argument that contains a slice
    slice_expr = None
    for arg in arg_exprs:
        slice_expr = find_slice_in_expr(arg)
        if slice_expr:
            break

    if not slice_expr or not slice_expr.end:
        return None

    # The original function call: Sum(s[..i])
    call = CallExpr(
        loc=func.loc,
        func=IdentExpr(loc=func.loc, name=func.name),
        args=arg_exprs
    )

    # The element at the slice boundary: s[i] (where s is the slice base, i is the slice end)
    element = IndexExpr(
        loc=func.loc,
        base=slice_expr.base,
        index=slice_expr.end
    )

    # The "pre-folding" expression: Sum(s[..i]) + s[i]
    pre_fold = BinaryExpr(
        loc=func.loc,
        op='+',
        left=call,
        right=element
    )

    # Create the incremented call: Sum(s[..i+1])
    new_end = increment_expr(slice_expr.end)
    incremented_args = [replace_slice_end(arg, slice_expr.end, new_end) for arg in arg_exprs]
    incremented_call = CallExpr(
        loc=func.loc,
        func=IdentExpr(loc=func.loc, name=func.name),
        args=incremented_args
    )

    # Generate detailed step-by-step calc block
    # Start from Sum(s[..i+1]) and work down to sum + s[i]

    slice_base_str = expr_to_string(slice_expr.base)  # e.g., "s"
    slice_end_str = expr_to_string(slice_expr.end)    # e.g., "i"
    new_end_str = expr_to_string(new_end)             # e.g., "i + 1"

    # The incremented slice: s[..i+1]
    inc_slice = f'{slice_base_str}[..{new_end_str}]'

    # Step 1: Sum(s[..i+1])
    step1 = expr_to_string(incremented_call)

    # Step 2: Unfold Sum definition: Sum(s[..|s|-1]) + s[|s|-1] with s := s[..i+1]
    # → Sum(s[..i+1][..|s[..i+1]|-1]) + s[..i+1][|s[..i+1]|-1]
    step2 = f'{func.name}({inc_slice}[..|{inc_slice}|-1]) + {inc_slice}[|{inc_slice}|-1]'

    # Step 3: Simplify |s[..i+1]|-1 = i for the index
    # → Sum(s[..i+1][..|s[..i+1]|-1]) + s[i]
    step3 = f'{func.name}({inc_slice}[..{slice_end_str}]) + {slice_base_str}[{slice_end_str}]'

    # Step 4: Key assertion: s[..i+1][..i] == s[..i]
    # → Sum(s[..i]) + s[i]
    step4 = f'{func.name}({slice_base_str}[..{slice_end_str}]) + {slice_base_str}[{slice_end_str}]'

    # Step 5: Use invariant sum == Sum(s[..i])
    # → sum + s[i]
    step5 = f'sum + {slice_base_str}[{slice_end_str}]'

    lines = [
        f'{indent}calc {{',
        f'{indent}    {step1};',
        f'{indent}==  // unfold {func.name} definition',
        f'{indent}    {step2};',
        f'{indent}==  // simplify |{inc_slice}| - 1 == {slice_end_str}',
        f'{indent}    {step3};',
        f'{indent}==  {{ assert {inc_slice}[..{slice_end_str}] == {slice_base_str}[..{slice_end_str}]; }}',
        f'{indent}    {step4};',
        f'{indent}==  // invariant: sum == {func.name}({slice_base_str}[..{slice_end_str}])',
        f'{indent}    {step5};',
        f'{indent}}}'
    ]

    return '\n'.join(lines)


def find_function_calls(expr: Expr, func_name: str) -> List[CallExpr]:
    """Find all calls to a specific function in an expression."""
    calls = []

    if isinstance(expr, CallExpr):
        if isinstance(expr.func, IdentExpr) and expr.func.name == func_name:
            calls.append(expr)
        for arg in expr.args:
            calls.extend(find_function_calls(arg, func_name))
    elif isinstance(expr, BinaryExpr):
        calls.extend(find_function_calls(expr.left, func_name))
        calls.extend(find_function_calls(expr.right, func_name))
    elif isinstance(expr, UnaryExpr):
        calls.extend(find_function_calls(expr.operand, func_name))
    elif isinstance(expr, IndexExpr):
        calls.extend(find_function_calls(expr.base, func_name))
        calls.extend(find_function_calls(expr.index, func_name))
    elif isinstance(expr, SliceExpr):
        calls.extend(find_function_calls(expr.base, func_name))
        if expr.start:
            calls.extend(find_function_calls(expr.start, func_name))
        if expr.end:
            calls.extend(find_function_calls(expr.end, func_name))
    elif isinstance(expr, LengthExpr):
        calls.extend(find_function_calls(expr.operand, func_name))
    elif isinstance(expr, IfExpr):
        calls.extend(find_function_calls(expr.condition, func_name))
        calls.extend(find_function_calls(expr.then_expr, func_name))
        calls.extend(find_function_calls(expr.else_expr, func_name))
    elif isinstance(expr, ParenExpr):
        calls.extend(find_function_calls(expr.inner, func_name))

    return calls


def get_functions_used_in_invariants(ast: DafnyFile) -> Dict[str, List[CallExpr]]:
    """Find all function calls used in loop invariants and method ensures."""
    result = {}

    for method in ast.methods:
        # Check ensures clauses
        for ensures in method.ensures:
            for func in ast.functions:
                calls = find_function_calls(ensures, func.name)
                if calls:
                    if func.name not in result:
                        result[func.name] = []
                    result[func.name].extend(calls)

        # Check loop invariants
        if method.body:
            for stmt in method.body:
                if isinstance(stmt, WhileStmt):
                    for inv in stmt.invariants:
                        for func in ast.functions:
                            calls = find_function_calls(inv, func.name)
                            if calls:
                                if func.name not in result:
                                    result[func.name] = []
                                result[func.name].extend(calls)

    return result
