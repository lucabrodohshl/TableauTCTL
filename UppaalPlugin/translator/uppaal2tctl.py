#!/usr/bin/env python3
# ============================================================================
# uppaal2tctl.py — translate a UPPAAL query (+ model) into tctl_sat input
# ============================================================================
#
# Reference implementation of the "Check Satisfiability" translation.  Reads a
# UPPAAL model (.xml NTA) to classify identifiers and emit structural
# invariants, parses the UPPAAL query/property language, and emits a formula in
# the tctl_sat syntax together with the list of real-sorted (clock) variables.
#
# Locked semantics (see DESIGN.md):
#   * clocks  -> real-valued Z3 vars (emitted via --real-vars); NOT lifted to a
#               [a,b] modality.
#   * deadlock-> the query is REJECTED (our models are deadlock-free by
#               construction).
#   * scope   -> model present  : conjoin structural invariants (per-INSTANCE
#                                  exactly-one-location, int range bounds,
#                                  clock>=0) under AG.
#                model absent    : opaque atoms + a warning.
#
# This module is intentionally dependency-free (stdlib only): xml.etree for the
# model, a small hand-written tokenizer + Pratt parser for the query.
# ============================================================================

from __future__ import annotations

import argparse
import re
import sys
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple


# ============================================================================
# Model
# ============================================================================

@dataclass
class VarDecl:
    name: str
    kind: str                 # 'clock' | 'int' | 'bool' | 'const'
    lo: Optional[int] = None  # int range bounds (if any)
    hi: Optional[int] = None
    value: Optional[int] = None  # for const


@dataclass
class Template:
    name: str
    locations: Set[str] = field(default_factory=set)   # location NAMES
    locals: Dict[str, VarDecl] = field(default_factory=dict)


@dataclass
class Instance:
    name: str
    template: str


@dataclass
class Model:
    globals: Dict[str, VarDecl] = field(default_factory=dict)
    templates: Dict[str, Template] = field(default_factory=dict)
    instances: Dict[str, Instance] = field(default_factory=dict)  # inst name -> Instance
    warnings: List[str] = field(default_factory=list)

    def instance(self, name: str) -> Optional[Instance]:
        return self.instances.get(name)

    def template_of(self, inst_name: str) -> Optional[Template]:
        inst = self.instances.get(inst_name)
        return self.templates.get(inst.template) if inst else None


# ---- declaration scanner (C-like UPPAAL declarations; common forms) --------

_CLOCK_RE = re.compile(r"\bclock\s+([^;]+);")
_BOOL_RE = re.compile(r"\bbool\s+([^;]+);")
# int  v;   |  int[lo,hi] v, w;   |  const int N = 5;
_CONST_RE = re.compile(r"\bconst\s+int\s+(\w+)\s*=\s*(-?\d+)\s*;")
_INT_RE = re.compile(r"\bint\s*(?:\[\s*(-?\d+)\s*,\s*(-?\d+)\s*\])?\s+([^;]+);")


def _names(decl_body: str) -> List[str]:
    """Split 'x, y = 0, z' into ['x','y','z'] (drop initialisers/array dims)."""
    out = []
    for part in decl_body.split(","):
        part = part.split("=")[0].strip()
        part = re.sub(r"\[.*?\]", "", part).strip()   # drop array dims
        m = re.match(r"^(\w+)", part)
        if m:
            out.append(m.group(1))
    return out


def scan_declarations(text: str, table: Dict[str, VarDecl]) -> None:
    """Populate `table` with clock/int/bool/const declarations found in `text`."""
    if not text:
        return
    # strip // and /* */ comments
    text = re.sub(r"//[^\n]*", " ", text)
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    for m in _CONST_RE.finditer(text):
        table[m.group(1)] = VarDecl(m.group(1), "const", value=int(m.group(2)))
    for m in _CLOCK_RE.finditer(text):
        for n in _names(m.group(1)):
            table[n] = VarDecl(n, "clock")
    for m in _BOOL_RE.finditer(text):
        for n in _names(m.group(1)):
            table[n] = VarDecl(n, "bool")
    for m in _INT_RE.finditer(text):
        lo = int(m.group(1)) if m.group(1) is not None else None
        hi = int(m.group(2)) if m.group(2) is not None else None
        for n in _names(m.group(3)):
            if n in table and table[n].kind == "const":
                continue
            table[n] = VarDecl(n, "int", lo=lo, hi=hi)


def parse_model(xml_path: str) -> Model:
    tree = ET.parse(xml_path)
    nta = tree.getroot()
    model = Model()

    # global declarations
    gdecl = nta.find("declaration")
    scan_declarations(gdecl.text if gdecl is not None else "", model.globals)

    # templates
    for tmpl in nta.findall("template"):
        nm = tmpl.find("name")
        tname = (nm.text or "").strip() if nm is not None else ""
        t = Template(tname)
        ldecl = tmpl.find("declaration")
        scan_declarations(ldecl.text if ldecl is not None else "", t.locals)
        for loc in tmpl.findall("location"):
            ln = loc.find("name")
            if ln is not None and ln.text:
                t.locations.add(ln.text.strip())
        model.templates[tname] = t

    # system / instantiation
    sysdecl = nta.find("system")
    parse_system(sysdecl.text if sysdecl is not None else "", model)
    return model


def parse_system(text: str, model: Model) -> None:
    """Extract process instances from the system declaration.

    Handles the common forms:
        name = Template(args);        -> instance `name` of Template
        system a, b, c;               -> the listed instances/templates
        system Template;              -> one anonymous instance named Template
    Process arrays / unbounded instantiation -> warning (instances left implicit).
    """
    if not text:
        return
    text = re.sub(r"//[^\n]*", " ", text)
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)

    # named instantiations:  ident = Template ( ... ) ;
    for m in re.finditer(r"\b(\w+)\s*=\s*(\w+)\s*\(", text):
        inst, tmpl = m.group(1), m.group(2)
        if tmpl in model.templates:
            model.instances[inst] = Instance(inst, tmpl)

    # the `system ...;` list
    sm = re.search(r"\bsystem\s+([^;]+);", text)
    if sm:
        for nm in [x.strip() for x in sm.group(1).split(",")]:
            nm = re.sub(r"\(.*?\)", "", nm).strip()
            if not nm:
                continue
            if nm in model.instances:
                continue
            if nm in model.templates:
                # direct template in system -> one anonymous instance named nm
                model.instances[nm] = Instance(nm, nm)
            else:
                model.warnings.append(
                    f"system references '{nm}' which is not a known template/"
                    f"instance (process array or partial instantiation?); "
                    f"exactly-one-location not enforced for it")


# ============================================================================
# Query tokenizer
# ============================================================================

# longest-match first
_TOKEN_SPEC = [
    ("WS",     r"[ \t\r\n]+"),
    ("LEADSTO", r"-->"),
    ("DIAM",   r"<>"),
    ("BOX",    r"\[\s*\]"),
    ("LE",     r"<="),
    ("GE",     r">="),
    ("EQ",     r"=="),
    ("NE",     r"!="),
    ("AND",    r"&&"),
    ("OR",     r"\|\|"),
    ("LT",     r"<"),
    ("GT",     r">"),
    ("ASSIGN_EQ", r"="),          # tolerate single '=' as equality in predicates
    ("NOT",    r"!"),
    ("LBRK",   r"\["),
    ("RBRK",   r"\]"),
    ("LPAR",   r"\("),
    ("RPAR",   r"\)"),
    ("COMMA",  r","),
    ("DOT",    r"\."),
    ("PLUS",   r"\+"),
    ("MINUS",  r"-"),
    ("STAR",   r"\*"),
    ("INT",    r"\d+"),
    ("IDENT",  r"[A-Za-z_]\w*"),
]
_TOKEN_RE = re.compile("|".join(f"(?P<{n}>{p})" for n, p in _TOKEN_SPEC))

_KEYWORDS = {"and": "AND", "or": "OR", "not": "NOT", "imply": "IMPLY",
             "true": "TRUE", "false": "FALSE", "deadlock": "DEADLOCK",
             "inf": "INF", "E": "E", "A": "A",
             "forall": "FORALL", "exists": "EXISTS"}

# property forms we do not handle (statistical / value / strategy)
_UNSUPPORTED_PREFIX = re.compile(r"^\s*(Pr\s*[\[{]|sup\s*[:{]|inf\s*[:{]|"
                                 r"simulate\b|E\s*\[|strategy\b|"
                                 r"\w+\s*=\s*(minE|maxE)\b|control\s*:)")


class Tok:
    __slots__ = ("kind", "val", "pos")

    def __init__(self, kind, val, pos):
        self.kind, self.val, self.pos = kind, val, pos

    def __repr__(self):
        return f"{self.kind}({self.val})"


class TranslationError(Exception):
    """Raised for an UNSUPPORTED / rejected query (caught by translate())."""


def tokenize(s: str) -> List[Tok]:
    toks: List[Tok] = []
    i = 0
    for m in _TOKEN_RE.finditer(s):
        if m.lastgroup == "WS":
            continue
        kind, val = m.lastgroup, m.group()
        if kind == "IDENT" and val in _KEYWORDS:
            kind = _KEYWORDS[val]
        toks.append(Tok(kind, val, m.start()))
        i = m.end()
    if i != len(s.rstrip()):
        # unmatched tail
        pass
    toks.append(Tok("EOF", "", len(s)))
    return toks


# ============================================================================
# Query AST
# ============================================================================

@dataclass
class Quant:        # E<>/A[]/E[]/A<> [optional bound] over a predicate
    quant: str      # 'E' | 'A'
    path: str       # 'F' (<>) | 'G' ([])
    bound: Optional[Tuple[int, object]]   # (a, b|'inf') or None
    pred: "Node"


@dataclass
class LeadsTo:
    lhs: "Node"
    rhs: "Node"


@dataclass
class Node:          # state-predicate node
    op: str          # 'and','or','not','imply', cmp ops, '+','-','*',
                     # 'loc','var','const','int','true','false','deadlock'
    kids: List["Node"] = field(default_factory=list)
    name: str = ""   # for loc/var: dotted name; for int: literal
    ival: int = 0


# ============================================================================
# Pratt parser for the query
# ============================================================================

class Parser:
    def __init__(self, toks: List[Tok]):
        self.t = toks
        self.i = 0

    def peek(self) -> Tok:
        return self.t[self.i]

    def next(self) -> Tok:
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, kind: str) -> Tok:
        if self.peek().kind != kind:
            raise TranslationError(f"expected {kind}, got {self.peek()}")
        return self.next()

    # ---- query level ----
    def parse_query(self):
        k = self.peek().kind
        if k in ("E", "A"):
            return self.parse_quant()
        # else: a leads-to  (pred --> pred)
        lhs = self.parse_pred()
        if self.peek().kind == "LEADSTO":
            self.next()
            rhs = self.parse_pred()
            return LeadsTo(lhs, rhs)
        if self.peek().kind != "EOF":
            raise TranslationError(f"trailing tokens after predicate: {self.peek()}")
        # bare predicate (no path operator) — treat as E<> reachability? UPPAAL
        # requires an operator; reject for clarity.
        raise TranslationError("query has no path operator (E<>, A[], E[], A<>, -->)")

    def parse_quant(self) -> Quant:
        q = self.next().kind          # 'E' or 'A'
        pk = self.peek().kind
        if pk == "DIAM":
            self.next(); path = "F"
        elif pk == "BOX":
            self.next(); path = "G"
        else:
            raise TranslationError(f"expected <> or [] after {q}, got {self.peek()}")
        bound = None
        if self.peek().kind == "LBRK":
            bound = self.parse_bound()
        pred = self.parse_pred()
        if self.peek().kind != "EOF":
            raise TranslationError(f"trailing tokens after query: {self.peek()}")
        return Quant(q, path, bound, pred)

    def parse_bound(self):
        self.expect("LBRK")
        a = int(self.expect("INT").val)
        self.expect("COMMA")
        if self.peek().kind == "INF":
            self.next(); b = "inf"
        else:
            b = int(self.expect("INT").val)
        self.expect("RBRK")
        if b != "inf" and a >= b:
            raise TranslationError(f"punctual/empty time bound [{a},{b}] (need a<b)")
        return (a, b)

    # ---- predicate level (precedence climbing) ----
    # imply  <  or  <  and  <  not  <  cmp  <  add  <  mul  <  atom
    def parse_pred(self) -> Node:
        return self.parse_imply()

    def parse_imply(self) -> Node:
        lhs = self.parse_or()
        if self.peek().kind == "IMPLY":
            self.next()
            rhs = self.parse_imply()
            return Node("imply", [lhs, rhs])
        return lhs

    def parse_or(self) -> Node:
        lhs = self.parse_and()
        while self.peek().kind == "OR":
            self.next()
            lhs = Node("or", [lhs, self.parse_and()])
        return lhs

    def parse_and(self) -> Node:
        lhs = self.parse_not()
        while self.peek().kind == "AND":
            self.next()
            lhs = Node("and", [lhs, self.parse_not()])
        return lhs

    def parse_not(self) -> Node:
        if self.peek().kind == "NOT":
            self.next()
            return Node("not", [self.parse_not()])
        return self.parse_cmp()

    _CMP = {"LE": "<=", "LT": "<", "GE": ">=", "GT": ">",
            "EQ": "=", "ASSIGN_EQ": "=", "NE": "!="}

    def parse_cmp(self) -> Node:
        lhs = self.parse_add()
        k = self.peek().kind
        if k in self._CMP:
            self.next()
            rhs = self.parse_add()
            return Node(self._CMP[k], [lhs, rhs])
        return lhs

    def parse_add(self) -> Node:
        lhs = self.parse_mul()
        while self.peek().kind in ("PLUS", "MINUS"):
            op = "+" if self.next().kind == "PLUS" else "-"
            lhs = Node(op, [lhs, self.parse_mul()])
        return lhs

    def parse_mul(self) -> Node:
        lhs = self.parse_atom()
        while self.peek().kind == "STAR":
            self.next()
            lhs = Node("*", [lhs, self.parse_atom()])
        return lhs

    def parse_atom(self) -> Node:
        tok = self.peek()
        if tok.kind == "LPAR":
            self.next()
            inner = self.parse_pred()
            self.expect("RPAR")
            return inner
        if tok.kind == "TRUE":
            self.next(); return Node("true")
        if tok.kind == "FALSE":
            self.next(); return Node("false")
        if tok.kind == "DEADLOCK":
            self.next()
            raise TranslationError(
                "query uses 'deadlock'; by construction all witness models are "
                "deadlock-free, so deadlock queries are not considered (yet)")
        if tok.kind in ("FORALL", "EXISTS"):
            raise TranslationError(f"'{tok.val}' quantifier not supported yet")
        if tok.kind == "MINUS":
            self.next()
            return Node("-", [Node("int", name="0", ival=0), self.parse_atom()])
        if tok.kind == "INT":
            self.next()
            return Node("int", name=tok.val, ival=int(tok.val))
        if tok.kind == "IDENT":
            return self.parse_dotted()
        raise TranslationError(f"unexpected token {tok}")

    def parse_dotted(self) -> Node:
        parts = [self.expect("IDENT").val]
        while self.peek().kind == "DOT":
            self.next()
            parts.append(self.expect("IDENT").val)
        # array index?
        if self.peek().kind == "LBRK":
            self.next()
            idx = self.parse_add()
            self.expect("RBRK")
            if idx.op != "int":
                raise TranslationError(
                    f"non-constant array index in '{'.'.join(parts)}[...]' not supported")
            parts[-1] = f"{parts[-1]}_{idx.ival}"
        # function call?
        if self.peek().kind == "LPAR":
            raise TranslationError(
                f"function call '{'.'.join(parts)}(...)' in a predicate not supported")
        return Node("name", name=".".join(parts))


# ============================================================================
# Emission: classify identifiers, build invariants, render tctl_sat syntax
# ============================================================================

def _atom(name: str) -> str:
    return name.replace(".", "_")


@dataclass
class Emit:
    model: Optional[Model]
    real_vars: Set[str] = field(default_factory=set)
    int_vars: Dict[str, VarDecl] = field(default_factory=dict)
    clocks: Set[str] = field(default_factory=set)
    # per-instance -> set of mentioned location atoms (for exactly-one)
    inst_locs: Dict[str, Set[str]] = field(default_factory=dict)
    warnings: List[str] = field(default_factory=list)

    def classify_name(self, dotted: str) -> str:
        """Return the tctl_sat rendering of a leaf name and record its kind."""
        m = self.model
        parts = dotted.split(".")
        if m is None:
            # no model: opaque boolean atom
            return _atom(dotted)

        if len(parts) == 2:
            inst, member = parts
            t = m.template_of(inst)
            if t is not None and member in t.locations:
                atom = _atom(dotted)
                self.inst_locs.setdefault(inst, set()).add(atom)
                return atom
            if t is not None and member in t.locals:
                return self._var(dotted, t.locals[member])
            # instance exists but member unknown -> treat as location atom
            if inst in m.instances:
                atom = _atom(dotted)
                self.inst_locs.setdefault(inst, set()).add(atom)
                self.warnings.append(
                    f"'{dotted}': '{member}' not found in template of '{inst}'; "
                    f"treated as a location atom")
                return atom
            # unknown instance -> opaque atom
            self.warnings.append(f"'{dotted}': unknown process instance '{inst}'; "
                                 f"treated as opaque atom")
            return _atom(dotted)

        if len(parts) == 1:
            n = parts[0]
            d = m.globals.get(n)
            if d is not None:
                if d.kind == "const":
                    return str(d.value)
                if d.kind == "bool":
                    return _atom(n)
                return self._var(n, d)
            # unknown bare name -> opaque boolean atom
            return _atom(n)

        # deeper dotted name -> opaque atom
        return _atom(dotted)

    def _var(self, dotted: str, d: VarDecl) -> str:
        a = _atom(dotted)
        if d.kind == "clock":
            self.real_vars.add(a)
            self.clocks.add(a)
        elif d.kind == "int":
            self.int_vars[a] = VarDecl(a, "int", d.lo, d.hi)
        return a

    # ---- render a predicate Node to tctl_sat string ----
    def render(self, n: Node) -> str:
        op = n.op
        if op == "true":
            return "true"
        if op == "false":
            return "false"
        if op == "int":
            return n.name
        if op == "name":
            return self.classify_name(n.name)
        if op == "not":
            return f"!({self.render(n.kids[0])})"
        if op in ("and", "or", "imply"):
            sym = {"and": "&", "or": "|", "imply": "->"}[op]
            return f"({self.render(n.kids[0])} {sym} {self.render(n.kids[1])})"
        if op == "!=":
            return f"!({self.render(n.kids[0])} = {self.render(n.kids[1])})"
        if op in ("<=", "<", ">=", ">", "="):
            return f"({self.render(n.kids[0])} {op} {self.render(n.kids[1])})"
        if op in ("+", "-", "*"):
            return f"({self.render(n.kids[0])} {op} {self.render(n.kids[1])})"
        raise TranslationError(f"cannot render node op '{op}'")

    # ---- structural invariants (model-aware) ----
    def invariants(self) -> Optional[str]:
        if self.model is None:
            return None
        conj: List[str] = []
        # 4a. exactly-one location per INSTANCE (mentioned + _other sentinel)
        for inst, locs in sorted(self.inst_locs.items()):
            t = self.model.template_of(inst)
            # only enforce if the instance is a real, bounded instance
            atoms = sorted(locs)
            # if the template has locations beyond those mentioned, add a sentinel
            if t is not None and len(t.locations) > len({a.split("_", 1)[1] for a in atoms if "_" in a}):
                atoms = atoms + [f"{_atom(inst)}_other"]
            if len(atoms) >= 2:
                conj.append(self._exactly_one(atoms))
            elif len(atoms) == 1:
                # single mentioned location + (implicit) elsewhere: no constraint
                pass
        # 4b. int range bounds
        for a, d in sorted(self.int_vars.items()):
            if d.lo is not None:
                conj.append(f"({d.lo} <= {a})")
            if d.hi is not None:
                conj.append(f"({a} <= {d.hi})")
        # 4c. clock non-negativity
        for c in sorted(self.clocks):
            conj.append(f"({c} >= 0)")
        if not conj:
            return None
        return " & ".join(conj)

    @staticmethod
    def _exactly_one(atoms: List[str]) -> str:
        at_least = "(" + " | ".join(atoms) + ")"
        excl = []
        for i in range(len(atoms)):
            for j in range(i + 1, len(atoms)):
                excl.append(f"!({atoms[i]} & {atoms[j]})")
        if excl:
            return "(" + at_least + " & " + " & ".join(excl) + ")"
        return at_least


# ============================================================================
# Top-level translate
# ============================================================================

@dataclass
class Result:
    ok: bool
    formula: str = ""
    real_vars: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    reason: str = ""          # set when ok == False


def _path_str(quant: str, path: str, bound, body: str) -> str:
    """Render E/A + F/G (+ bound) over an already-rendered body."""
    b = ""
    if bound is not None:
        a, hi = bound
        b = f"[{a},{hi}]"
    op = {("E", "F"): "EF", ("A", "G"): "AG",
          ("E", "G"): "EG", ("A", "F"): "AF"}[(quant, path)]
    return f"{op}{b} ({body})"


def translate(query: str, model: Optional[Model]) -> Result:
    if _UNSUPPORTED_PREFIX.match(query):
        return Result(False, reason="unsupported query form (statistical / "
                      "value / strategy query: Pr[], sup/inf, simulate, E[], "
                      "strategy)")
    try:
        toks = tokenize(query)
        ast = Parser(toks).parse_query()
        em = Emit(model)

        if isinstance(ast, Quant):
            body = em.render(ast.pred)
            core = _path_str(ast.quant, ast.path, ast.bound, body)
        elif isinstance(ast, LeadsTo):
            lhs = em.render(ast.lhs)
            rhs = em.render(ast.rhs)
            # p --> q  ==  AG( p -> AF q )
            core = f"AG (({lhs}) -> AF ({rhs}))"
        else:
            return Result(False, reason="unrecognised query shape")

        inv = em.invariants()
        if inv:
            # query  &  AG( structural invariants )
            formula = f"({core}) & AG ({inv})"
        else:
            formula = core

        warns = list(em.warnings)
        if model is None:
            warns.append("no model supplied: identifiers treated as opaque "
                         "atoms; structural contradictions (e.g. two locations "
                         "of one process) are NOT detected")
        else:
            warns = model.warnings + warns
        return Result(True, formula=formula,
                      real_vars=sorted(em.real_vars), warnings=warns)
    except TranslationError as e:
        return Result(False, reason=str(e))


# ============================================================================
# CLI
# ============================================================================

def _read_queries(qpath: str) -> List[str]:
    out = []
    with open(qpath) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("//") or line.startswith("#"):
                continue
            out.append(line)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="Translate UPPAAL queries to tctl_sat input.")
    ap.add_argument("--model", help="UPPAAL .xml model (enables model-aware invariants)")
    ap.add_argument("--query", help="a single query string")
    ap.add_argument("--queries", help="a .q file (one query per line)")
    ap.add_argument("--json", action="store_true", help="emit JSON")
    args = ap.parse_args()

    model = parse_model(args.model) if args.model else None

    queries: List[str] = []
    if args.query:
        queries.append(args.query)
    if args.queries:
        queries.extend(_read_queries(args.queries))
    if not queries:
        print("no query given (use --query or --queries)", file=sys.stderr)
        return 2

    results = []
    for q in queries:
        r = translate(q, model)
        results.append((q, r))

    if args.json:
        import json
        print(json.dumps([{
            "query": q, "ok": r.ok, "formula": r.formula,
            "real_vars": r.real_vars, "warnings": r.warnings, "reason": r.reason,
        } for q, r in results], indent=2))
        return 0

    for q, r in results:
        print(f"# query: {q}")
        if r.ok:
            print(f"  formula : {r.formula}")
            if r.real_vars:
                print(f"  real-vars: {','.join(r.real_vars)}")
            for w in r.warnings:
                print(f"  warning : {w}")
        else:
            print(f"  REJECTED: {r.reason}")
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
