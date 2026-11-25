"""Streaming helpers for lean4export NDJSON files (format 3.x), shared by run.py and reduce.py.

An export is a sequence of lines: the `meta` line, names (`in`), levels (`il`), expressions
(`ie`) and declaration records (`axiom`, `def`, `thm`, `opaque`, `quot`, `inductive`; an
`inductive` record carries a whole mutual block). Every record refers only to ids bound on
earlier lines, and ids need not be dense, so dropping lines that nothing kept refers to
leaves a valid export.

The functions here never hold the whole file: a pass reads it line by line and keeps, per
expression id, one byte (and for `closure`, the expression's children).
"""
import json

DECL_KEYS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
# Expression fields that hold expression ids.
_EXPR_CHILDREN = {
    "app": ("fn", "arg"),
    "lam": ("type", "body"),
    "forallE": ("type", "body"),
    "letE": ("type", "value", "body"),
    "proj": ("struct",),
    "mdata": ("expr",),
}


def norm_name(s):
    """A declaration name as both checkers print it, without Lean's «» escapes."""
    return s.replace("«", "").replace("»", "")


def lines(path):
    with open(path, "rb") as f:
        for raw in f:
            yield raw


def decl_kind(obj):
    for k in DECL_KEYS:
        if k in obj:
            return k
    return None


def decl_names(kind, body):
    """Name ids of the constants a declaration record introduces."""
    if kind == "inductive":
        return ([t["name"] for t in body.get("types", [])]
                + [c["name"] for c in body.get("ctors", [])]
                + [r["name"] for r in body.get("recs", [])])
    return [body["name"]]


def decl_roots(kind, body):
    """Expression ids a declaration record refers to."""
    if kind in ("axiom", "quot"):
        return [body["type"]]
    if kind in ("def", "thm", "opaque"):
        return [body["type"], body["value"]]
    out = ([t["type"] for t in body.get("types", [])]
           + [c["type"] for c in body.get("ctors", [])])
    for r in body.get("recs", []):
        out.append(r["type"])
        out.extend(rule["rhs"] for rule in r.get("rules", []))
    return out


def expr_children(obj):
    """(children expression ids, constant name id or None) of an `ie` record."""
    for k, fields in _EXPR_CHILDREN.items():
        if k in obj:
            v = obj[k]
            return [v[f] for f in fields], None
    if "const" in obj:
        return [], obj["const"]["name"]
    return [], None


class Names:
    """Name ids to strings (only the names that are asked for are rendered)."""

    def __init__(self):
        self.parts = {0: None}

    def add(self, obj):
        if "str" in obj:
            self.parts[obj["in"]] = (obj["str"]["pre"], obj["str"]["str"])
        else:
            self.parts[obj["in"]] = (obj["num"]["pre"], str(obj["num"]["i"]))

    def render(self, i):
        out = []
        while i and self.parts.get(i):
            pre, s = self.parts[i]
            out.append(s)
            i = pre
        return ".".join(reversed(out))


def classify(obj):
    """'name', 'level', 'expr', 'meta', a declaration key, or None."""
    if "in" in obj:
        return "name"
    if "il" in obj:
        return "level"
    if "ie" in obj:
        return "expr"
    if "meta" in obj:
        return "meta"
    return decl_kind(obj)


def parse(raw):
    """(object, classify(object)); a line that is not a JSON object is ({}, None), and is
    left for the checkers to report."""
    try:
        obj = json.loads(raw)
    except ValueError:
        return {}, None
    if not isinstance(obj, dict):
        return {}, None
    return obj, classify(obj)


class Index:
    """What one pass learns about an export: its declaration records, in file order.

    decls: list of (line number, kind, [constant names], [name ids]); names: Names."""

    def __init__(self, path):
        self.path = path
        self.names = Names()
        self.decls = []
        self.meta = None
        for no, raw in enumerate(lines(path)):
            obj, k = parse(raw)
            if k == "name":
                self.names.add(obj)
            elif k in DECL_KEYS:
                body = obj[k]
                ids = decl_names(k, body)
                self.decls.append((no, k, [self.names.render(i) for i in ids], ids))
            elif k == "meta":
                self.meta = obj["meta"]
        self.by_name = {}
        for d in self.decls:
            for n in d[2]:
                self.by_name[norm_name(n)] = d

    def constants(self):
        return [n for d in self.decls for n in d[2]]


def as_axiom(obj):
    """A `thm` record as an axiom with the same name, universe parameters and type."""
    b = obj["thm"]
    return {"axiom": {"name": b["name"], "levelParams": b["levelParams"], "type": b["type"],
                      "isUnsafe": False}}


def rewrite(src, dst, drop_lines=(), drop_names=(), axiomatize=()):
    """Copy src to dst without the declaration records on drop_lines, without those that
    introduce one of drop_names (name strings, normalized), and without every record that
    depends on a dropped one, with the theorems named in axiomatize turned into axioms.

    Repeats the pass until no new record is dropped (a constant can be used by an
    expression that comes before its declaration). Returns the set of dropped constant
    names (normalized)."""
    drop_lines = set(drop_lines)
    drop = set(norm_name(n) for n in drop_names)
    axiomatize = set(norm_name(n) for n in axiomatize)
    while True:
        names = Names()
        bad_names = set()   # name ids of dropped constants
        bad = bytearray()   # per expression id: 1 if it mentions a dropped constant
        dropped = set()
        dropped_lines = set()
        # name ids are only known while reading, so bad_names is filled as decls are seen
        # and on later passes from `drop`.
        for no, raw in enumerate(lines(src)):
            obj, k = parse(raw)
            if k == "name":
                names.add(obj)
                if norm_name(names.render(obj["in"])) in drop:
                    bad_names.add(obj["in"])
            elif k in DECL_KEYS:
                body = obj[k]
                ns = [norm_name(names.render(i)) for i in decl_names(k, body)]
                roots = decl_roots(k, body)
                if k == "thm" and ns[0] in axiomatize:
                    roots = roots[:1]
                if no in drop_lines or any(n in drop for n in ns) or any(
                        r < len(bad) and bad[r] for r in roots):
                    dropped.update(ns)
                    dropped_lines.add(no)
                    bad_names.update(decl_names(k, body))
            elif k == "expr":
                ie = obj["ie"]
                ch, c = expr_children(obj)
                v = 1 if (c is not None and c in bad_names) or any(
                    x < len(bad) and bad[x] for x in ch) else 0
                if v:
                    if ie >= len(bad):
                        bad.extend(b"\0" * (ie + 1 - len(bad) + (1 << 16)))
                    bad[ie] = 1
        if dropped <= drop:
            break
        drop |= dropped
    with open(dst, "wb") as out:
        names = Names()
        for no, raw in enumerate(lines(src)):
            if no in dropped_lines:
                continue
            if not axiomatize:
                out.write(raw)
                continue
            obj, k = parse(raw)
            if k == "name":
                names.add(obj)
            elif k == "thm":
                if norm_name(names.render(obj["thm"]["name"])) in axiomatize:
                    raw = (json.dumps(as_axiom(obj), separators=(",", ":")) + "\n").encode()
            out.write(raw)
    return dropped


class Graph:
    """The whole export in memory, compactly: for `closure`. Expression children are kept
    in flat arrays, so a large export takes a few bytes per expression."""

    def __init__(self, path):
        from array import array
        self.path = path
        self.names = Names()
        self.kids_start = array("q")   # per expression line, in file order
        self.kids = array("q")         # children ids; a constant is -(name id) - 1
        self.expr_pos = {}             # expression id -> index into kids_start
        self.decl_of = {}              # name id -> line number of its declaration record
        self.decl_roots = {}           # line number -> (kind, name ids, root expr ids)
        self.line_kind = []            # per line: 'n', 'l', 'e', 'd', 'm'
        for no, raw in enumerate(lines(path)):
            obj, k = parse(raw)
            if k == "name":
                self.names.add(obj)
                self.line_kind.append(("n", obj["in"]))
            elif k in DECL_KEYS:
                body = obj[k]
                ids = decl_names(k, body)
                for i in ids:
                    self.decl_of[i] = no
                self.decl_roots[no] = (k, ids, decl_roots(k, body))
                self.line_kind.append(("d", no))
            elif k == "level":
                self.line_kind.append(("l", obj["il"]))
            elif k == "expr":
                ie = obj["ie"]
                ch, c = expr_children(obj)
                self.expr_pos[ie] = len(self.kids_start)
                self.kids_start.append(len(self.kids))
                self.kids.extend(ch)
                if c is not None:
                    self.kids.append(-c - 1)
                self.line_kind.append(("e", ie))
            else:
                self.line_kind.append(("m", 0))
        self.kids_start.append(len(self.kids))

    def name_id(self, name):
        want = norm_name(name)
        for i, d in self.decl_of.items():
            if norm_name(self.names.render(i)) == want:
                return i
        return None

    def closure(self, start_lines, value_free=()):
        """Line numbers of the declaration records needed by start_lines (themselves
        included). Records in value_free are taken as axioms: only their types count."""
        need_decls = set()
        stack = list(start_lines)
        seen_expr = set()
        while stack:
            no = stack.pop()
            if no in need_decls:
                continue
            need_decls.add(no)
            k, _, roots = self.decl_roots[no]
            if no in value_free and k in ("def", "thm", "opaque"):
                roots = roots[:1]
            work = list(roots)
            while work:
                e = work.pop()
                if e in seen_expr:
                    continue
                seen_expr.add(e)
                p = self.expr_pos[e]
                for x in self.kids[self.kids_start[p]:self.kids_start[p + 1]]:
                    if x < 0:
                        d = self.decl_of.get(-x - 1)
                        if d is not None and d not in need_decls:
                            stack.append(d)
                    else:
                        work.append(x)
        return need_decls

    def write(self, dst, decl_lines, value_free=()):
        """Write the records on decl_lines (with those in value_free made axioms, or for a
        definition an opaque-free axiom) and every name, level and expression line: lines
        nothing refers to are harmless, but expressions are pruned to those reachable."""
        keep_expr = set()
        for no in decl_lines:
            k, _, roots = self.decl_roots[no]
            if no in value_free and k in ("def", "thm", "opaque"):
                roots = roots[:1]
            work = list(roots)
            while work:
                e = work.pop()
                if e in keep_expr:
                    continue
                keep_expr.add(e)
                p = self.expr_pos[e]
                work.extend(x for x in self.kids[self.kids_start[p]:self.kids_start[p + 1]]
                            if x >= 0)
        with open(dst, "wb") as out:
            for no, raw in enumerate(lines(self.path)):
                kind, v = self.line_kind[no]
                if kind == "e" and v not in keep_expr:
                    continue
                if kind == "d":
                    if no not in decl_lines:
                        continue
                    if no in value_free:
                        obj = json.loads(raw)
                        k = decl_kind(obj)
                        if k in ("def", "thm", "opaque"):
                            b = obj[k]
                            obj = {"axiom": {"name": b["name"], "levelParams": b["levelParams"],
                                             "type": b["type"], "isUnsafe": False}}
                            raw = (json.dumps(obj, separators=(",", ":")) + "\n").encode()
                out.write(raw)
