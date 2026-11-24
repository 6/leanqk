"""Small library for reading, building and mutating lean4export (format 3.x) files.

An export is a list of JSON records. Names ("in"), levels ("il") and
expressions ("ie") have their own id spaces; declarations refer to them by id.
`Export` keeps the records in order, hash-conses new terms against existing
ones, and inserts the new primitive records right before the declaration
that first needs them, so the output stays in dependency order.
"""

import json

EXPR_CHILDREN = ("fn", "arg", "type", "body", "value", "struct", "expr")
EXPR_KINDS = ("bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj",
              "natVal", "strVal", "mdata")
DECL_KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")


def dumps(rec):
    return json.dumps(rec, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def kind_of(rec):
    for k in rec:
        if k not in ("in", "il", "ie"):
            return k
    raise ValueError(rec)


class Export:
    def __init__(self, text):
        lines = [ln for ln in text.split("\n") if ln.strip()]
        self.meta = json.loads(lines[0])
        self.recs = [json.loads(ln) for ln in lines[1:]]
        self.pending = []
        self._index()

    # ----- indexing -------------------------------------------------------
    def _index(self):
        self.names = {0: ()}
        self.name_ids = {(): 0}
        self.levels = {0: ("zero",)}
        self.level_ids = {("zero",): 0}
        self.exprs = {}
        self.expr_ids = {}
        for r in self.recs:
            self._learn(r)

    def _learn(self, r):
        if "in" in r:
            i = r["in"]
            if "str" in r:
                n = self.names[r["str"]["pre"]] + (r["str"]["str"],)
            else:
                n = self.names[r["num"]["pre"]] + (r["num"]["i"],)
            self.names[i] = n
            self.name_ids.setdefault(n, i)
        elif "il" in r:
            i = r["il"]
            k = kind_of(r)
            key = (k, json.dumps(r[k], sort_keys=True))
            self.levels[i] = key
            self.level_ids.setdefault(key, i)
        elif "ie" in r:
            i = r["ie"]
            k = kind_of(r)
            key = (k, json.dumps(r[k], sort_keys=True))
            self.exprs[i] = (k, r[k])
            self.expr_ids.setdefault(key, i)

    def text(self):
        """Serialise, pulling every primitive record in front of its first user."""
        self.recs.extend(self.pending)
        self.pending = []
        where = {}
        for r in self.recs:
            for sp in ("in", "il", "ie"):
                if sp in r:
                    where[(sp, r[sp])] = r
        done = set()
        out = []

        def emit(r):
            stack = [(r, False)]
            while stack:
                x, ready = stack.pop()
                if id(x) in done:
                    continue
                if ready:
                    done.add(id(x))
                    out.append(x)
                    continue
                stack.append((x, True))
                for d in reversed(deps(x)):
                    y = where.get(d)
                    if y is not None and id(y) not in done:
                        stack.append((y, False))

        for r in self.recs:
            emit(r)
        self.recs = out
        return "\n".join([dumps(self.meta)] + [dumps(r) for r in out]) + "\n"

    def _fresh(self, space):
        table = {"in": self.names, "il": self.levels, "ie": self.exprs}[space]
        return max(table) + 1 if table else 0

    def _new(self, space, kind, payload, ids):
        key = (kind, json.dumps(payload, sort_keys=True))
        if key in ids:
            return ids[key]
        r = {space: self._fresh(space), kind: payload}
        self.pending.append(r)
        self._learn(r)
        return r[space]

    # ----- names ----------------------------------------------------------
    def name(self, s):
        """Id of a dotted name, created if missing (numeric parts not supported)."""
        parts = tuple(s.split(".")) if s else ()
        if parts in self.name_ids:
            return self.name_ids[parts]
        pre = self.name(".".join(parts[:-1]))
        r = {"in": self._fresh("in"), "str": {"pre": pre, "str": parts[-1]}}
        self.pending.append(r)
        self._learn(r)
        return r["in"]

    def name_str(self, i):
        return ".".join(str(p) for p in self.names[i])

    # ----- levels ---------------------------------------------------------
    def lzero(self):
        return 0

    def lsucc(self, l):
        return self._new("il", "succ", l, self.level_ids)

    def lmax(self, a, b):
        return self._new("il", "max", [a, b], self.level_ids)

    def limax(self, a, b):
        return self._new("il", "imax", [a, b], self.level_ids)

    def lparam(self, s):
        return self._new("il", "param", self.name(s), self.level_ids)

    def lnum(self, n):
        l = 0
        for _ in range(n):
            l = self.lsucc(l)
        return l

    # ----- expressions ----------------------------------------------------
    def _e(self, kind, payload):
        return self._new("ie", kind, payload, self.expr_ids)

    def bvar(self, i):
        return self._e("bvar", i)

    def sort(self, l):
        return self._e("sort", l)

    def const(self, s, us=()):
        return self._e("const", {"name": self.name(s), "us": list(us)})

    def app(self, f, *args):
        for a in args:
            f = self._e("app", {"fn": f, "arg": a})
        return f

    def pi(self, n, ty, body, bi="default"):
        return self._e("forallE", {"binderInfo": bi, "body": body, "name": self.name(n), "type": ty})

    def lam(self, n, ty, body, bi="default"):
        return self._e("lam", {"binderInfo": bi, "body": body, "name": self.name(n), "type": ty})

    def nat(self, v):
        return self._e("natVal", str(v))

    def str_(self, s):
        return self._e("strVal", s)

    def proj(self, type_name, idx, struct):
        return self._e("proj", {"idx": idx, "struct": struct, "typeName": self.name(type_name)})

    # ----- expression transforms ------------------------------------------
    def rebuild(self, e, fe=None, fl=None, depth=0, memo=None):
        """Rebuild expression `e` bottom-up.  `fe(id, kind, payload, depth)` may
        return a replacement id; `fl(level_id)` maps levels in sorts and consts."""
        if memo is None:
            memo = {}
        key = (e, depth)
        if key in memo:
            return memo[key]
        k, p = self.exprs[e]
        if fe is not None:
            r = fe(e, k, p, depth)
            if r is not None:
                memo[key] = r
                return r
        if k == "sort":
            out = self.sort(fl(p)) if fl else e
        elif k == "const":
            out = self._e("const", {"name": p["name"], "us": [fl(u) for u in p["us"]]}) if fl else e
        elif k in ("bvar", "natVal", "strVal"):
            out = e
        else:
            q = dict(p)
            for c in EXPR_CHILDREN:
                if c in q:
                    d = depth + 1 if (c == "body") else depth
                    q[c] = self.rebuild(q[c], fe, fl, d, memo)
            out = self._e(k, q)
        memo[key] = out
        return out

    def subst_const(self, e, old, new_id):
        """Replace every `const old` by expression `new_id`."""
        n = self.name(old)
        return self.rebuild(e, fe=lambda i, k, p, d: new_id if k == "const" and p["name"] == n else None)

    def map_levels(self, e, fl):
        return self.rebuild(e, fl=fl)

    def binders(self, e, kind="forallE"):
        """Split `e` into ([(name, type, binderInfo)], body)."""
        bs = []
        while self.exprs[e][0] == kind:
            p = self.exprs[e][1]
            bs.append((p["name"], p["type"], p["binderInfo"]))
            e = p["body"]
        return bs, e

    def close(self, bs, body, kind="lam"):
        for (n, t, bi) in reversed(bs):
            body = self._e(kind, {"binderInfo": bi, "body": body, "name": n, "type": t})
        return body

    def app_args(self, e):
        args = []
        while self.exprs[e][0] == "app":
            p = self.exprs[e][1]
            args.append(p["arg"])
            e = p["fn"]
        return e, list(reversed(args))

    def rfl_proof(self, ty):
        """For `ty = ∀ xs, @Eq.{u} T a b` build `fun xs => @Eq.refl.{u} T a`."""
        bs, body = self.binders(ty)
        f, args = self.app_args(body)
        fk, fp = self.exprs[f]
        assert fk == "const" and self.name_str(fp["name"]) == "Eq", "not an Eq statement"
        T, a, _ = args
        refl = self._e("const", {"name": self.name("Eq.refl"), "us": fp["us"]})
        return self.close(bs, self.app(refl, T, a))

    # ----- declarations ---------------------------------------------------
    def decl_index(self, name):
        n = self.name_ids[tuple(name.split("."))]
        for i, r in enumerate(self.recs):
            k = kind_of(r)
            if k in ("axiom", "def", "thm", "opaque", "quot") and r[k]["name"] == n:
                return i
            if k == "inductive":
                for part in ("types", "ctors", "recs"):
                    if any(x["name"] == n for x in r[k][part]):
                        return i
        raise KeyError(name)

    def decl(self, name):
        """The mutable info dict of a declaration (a type, ctor or rec for inductives)."""
        i = self.decl_index(name)
        r = self.recs[i]
        k = kind_of(r)
        if k != "inductive":
            return r[k]
        n = self.name_ids[tuple(name.split("."))]
        for part in ("types", "ctors", "recs"):
            for x in r[k][part]:
                if x["name"] == n:
                    return x
        raise KeyError(name)

    def add_decl(self, kind, info):
        self.recs.append({kind: info})

    def add_thm(self, name, ty, value, lps=()):
        info = {"all": [self.name(name)], "levelParams": [self.name(u) for u in lps],
                "name": self.name(name), "type": ty, "value": value}
        self.add_decl("thm", info)

    def add_def(self, name, ty, value, lps=(), safety="safe", hints="opaque"):
        info = {"all": [self.name(name)], "hints": hints, "levelParams": [self.name(u) for u in lps],
                "name": self.name(name), "safety": safety, "type": ty, "value": value}
        self.add_decl("def", info)

    def add_axiom(self, name, ty, lps=(), unsafe=False):
        info = {"isUnsafe": unsafe, "levelParams": [self.name(u) for u in lps],
                "name": self.name(name), "type": ty}
        self.add_decl("axiom", info)

    def remove_decl(self, name):
        del self.recs[self.decl_index(name)]


def deps(r):
    """(space, id) pairs a record refers to."""
    out = []
    N = lambda i: out.append(("in", i))
    L = lambda i: out.append(("il", i))
    E = lambda i: out.append(("ie", i))
    k = kind_of(r)
    p = r[k]
    if "in" in r:
        N(p["pre"])
    elif "il" in r:
        if k == "succ":
            L(p)
        elif k in ("max", "imax"):
            L(p[0]); L(p[1])
        elif k == "param":
            N(p)
    elif "ie" in r:
        if k == "sort":
            L(p)
        elif k == "const":
            N(p["name"]); [L(u) for u in p["us"]]
        elif k == "proj":
            N(p["typeName"]); E(p["struct"])
        elif k in ("bvar", "natVal", "strVal"):
            pass
        else:
            if "name" in p:
                N(p["name"])
            for c in EXPR_CHILDREN:
                if c in p:
                    E(p[c])
    else:
        infos = [p] if k != "inductive" else p["types"] + p["ctors"] + p["recs"]
        for x in infos:
            for f in ("name", "induct"):
                if f in x:
                    N(x[f])
            for f in ("levelParams", "all", "ctors"):
                for n in x.get(f, []):
                    N(n)
            for f in ("type", "value"):
                if f in x:
                    E(x[f])
            for rule in x.get("rules", []):
                N(rule["ctor"]); E(rule["rhs"])
    return out


def empty_export(meta):
    return Export(dumps(meta) + "\n")
