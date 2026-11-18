"""Secondary check on two lean4export (format 3.1.0) ndjson exports.

This is NOT the official comparator (`lake comparator`) and not an equivalent implementation.
It is an independent cross-check of the same three properties:
  1. every declaration in the exported Challenge closure is present in the Solution export with
     identical content (kind, universe parameters, type, value, inductive data), except that a
     target theorem's proof may differ (only its signature is compared);
  2. every target is a theorem in both exports;
  3. the axioms declared in the Solution export are among the permitted ones.
It compares the whole exported Challenge closure (the official tool traverses the declarations
reachable from the targets), so it can only be stricter on that closure.

Representation (exact, no hashing):
  * names are hash-consed structurally as anonymous / str(prefix, string) / num(prefix, nat),
    so `a.b` built from two components and the single component "a.b" stay distinct;
  * universe levels and expressions are hash-consed bottom-up into one table shared by both
    exports; two nodes are equal iff their constructor, literal fields and children are equal;
  * binder names and binder annotations are omitted from lambda/forall/let nodes, as in the
    kernel's notion of equality (Lean's `Expr` BEq is alpha-equivalence ignoring annotations,
    and the exporter shares nodes accordingly);
  * a duplicated name/level/expression id, or a duplicated declaration name, is rejected.

usage: python3 -I compare_exports.py CHALLENGE.ndjson SOLUTION.ndjson TARGETS.txt
exit status 0 only on PASS.
"""
import json
import sys

PERMITTED = {"propext", "Quot.sound", "Classical.choice"}
NAME_F = {"name", "typeName", "induct", "ctor", "param"}
EXPR_F = {"fn", "arg", "body", "type", "value", "struct", "rhs", "expr"}
LEVEL_F = {"sort", "succ"}
NAMELIST_F = {"levelParams", "all", "ctors"}
LEVELLIST_F = {"us", "max", "imax"}
DECL_KINDS = ("thm", "def", "axiom", "opaque", "quot", "inductive")


class ExportError(Exception):
    pass


class Table:
    """Global hash-consing table shared by both exports."""

    def __init__(self):
        self.ids = {}
        self.display = {}  # name gid -> dotted spelling, for messages only

    def intern(self, key):
        gid = self.ids.get(key)
        if gid is None:
            gid = len(self.ids)
            self.ids[key] = gid
        return gid


def load(path, table):
    names = {0: table.intern(("anonymous",))}
    table.display.setdefault(names[0], "")
    levels = {0: table.intern(("level", "zero"))}
    exprs = {}
    decls = {}

    def ref_name(i):
        try:
            return ("N", names[i])
        except KeyError:
            raise ExportError(f"undefined name id {i}")

    def ref_expr(i):
        try:
            return ("E", exprs[i])
        except KeyError:
            raise ExportError(f"undefined expression id {i}")

    def ref_level(i):
        try:
            return ("U", levels[i])
        except KeyError:
            raise ExportError(f"undefined level id {i}")

    def canon(obj):
        if isinstance(obj, dict):
            items = []
            for k in sorted(obj):
                v = obj[k]
                if k in NAME_F and isinstance(v, int):
                    items.append((k, ref_name(v)))
                elif k in EXPR_F and isinstance(v, int):
                    items.append((k, ref_expr(v)))
                elif k in LEVEL_F and isinstance(v, int):
                    items.append((k, ref_level(v)))
                elif k in NAMELIST_F and isinstance(v, list):
                    items.append((k, tuple(ref_name(x) if isinstance(x, int) else canon(x)
                                           for x in v)))
                elif k in LEVELLIST_F and isinstance(v, list):
                    items.append((k, tuple(ref_level(x) for x in v)))
                else:
                    items.append((k, canon(v)))
            return ("D",) + tuple(items)
        if isinstance(obj, list):
            return ("L",) + tuple(canon(x) for x in obj)
        return ("V", type(obj).__name__, obj)

    def define(table_local, i, gid, what):
        if i in table_local:
            raise ExportError(f"duplicate {what} id {i}")
        table_local[i] = gid

    with open(path, "r", encoding="utf-8") as f:
        for lineno, line in enumerate(f, 1):
            o = json.loads(line)
            if "meta" in o:
                continue
            if "in" in o:
                i = o.pop("in")
                if "str" in o:
                    s = o["str"]
                    key = ("str", ref_name(s["pre"])[1], s["str"])
                    disp = s["str"]
                elif "num" in o:
                    s = o["num"]
                    key = ("num", ref_name(s["pre"])[1], s["i"])
                    disp = str(s["i"])
                else:
                    raise ExportError(f"line {lineno}: unknown name record")
                gid = table.intern(key)
                pre = table.display[key[1]]
                table.display.setdefault(gid, (pre + "." if pre else "") + disp)
                define(names, i, gid, "name")
            elif "il" in o:
                i = o.pop("il")
                define(levels, i, table.intern(("level", canon(o))), "level")
            elif "ie" in o:
                i = o.pop("ie")
                for bk in ("lam", "forallE", "letE"):
                    if bk in o:
                        o[bk].pop("name", None)
                        o[bk].pop("binderInfo", None)
                define(exprs, i, table.intern(("expr", canon(o))), "expression")
            else:
                kinds = [k for k in DECL_KINDS if k in o]
                if len(kinds) != 1:
                    raise ExportError(f"line {lineno}: unknown record {list(o)[:3]}")
                kind = kinds[0]
                body = o[kind]
                c = canon(body)
                if kind == "inductive":
                    declared = ([t["name"] for t in body["types"]] +
                                [ct["name"] for ct in body["ctors"]] +
                                [r["name"] for r in body["recs"]])
                    entry = ("inductive", c, None)
                    for nid in declared:
                        n = ref_name(nid)[1]
                        if n in decls:
                            raise ExportError(f"duplicate declaration {table.display[n]}")
                        decls[n] = entry
                else:
                    n = ref_name(body["name"])[1]
                    if n in decls:
                        raise ExportError(f"duplicate declaration {table.display[n]}")
                    sig = (kind, canon({"levelParams": body.get("levelParams", []),
                                        "type": body["type"]}))
                    decls[n] = (kind, c, sig)
    return decls


def name_gid(table, dotted):
    """Structured name of a dotted target spelling whose components are plain strings."""
    gid = table.ids[("anonymous",)]
    for comp in dotted.split("."):
        key = ("str", gid, comp)
        if key not in table.ids:
            return None
        gid = table.ids[key]
    return gid


def main():
    chal_path, sol_path, tgt_path = sys.argv[1:4]
    targets = [l.strip() for l in open(tgt_path, encoding="utf-8") if l.strip()]
    table = Table()
    try:
        C = load(chal_path, table)
        print(f"challenge declarations: {len(C)}", flush=True)
        S = load(sol_path, table)
        print(f"solution declarations: {len(S)}", flush=True)
    except ExportError as e:
        print(f"SECONDARY CHECK FAIL: malformed export: {e}")
        sys.exit(1)
    failures = []
    tgids = set()
    for t in targets:
        g = name_gid(table, t)
        if g is None:
            failures.append(f"target {t} not found in either export")
            continue
        tgids.add(g)
        if g not in C or C[g][0] != "thm":
            failures.append(f"target {t} missing or not a theorem in Challenge")
        if g not in S or S[g][0] != "thm":
            failures.append(f"target {t} missing or not a theorem in Solution")
        elif g in C and C[g][2] != S[g][2]:
            failures.append(f"target {t}: statement differs between Challenge and Solution")
    sorry_gid = name_gid(table, "sorryAx")
    compared = 0
    for n, (kind, full, sig) in C.items():
        # sorryAx enters the Challenge closure only through the `sorry` proofs of the targets
        if n in tgids or n == sorry_gid:
            continue
        compared += 1
        if n not in S:
            failures.append(f"{table.display[n]} ({kind}) in Challenge closure but absent from Solution")
        elif S[n][0] != kind or S[n][1] != full:
            failures.append(f"{table.display[n]} ({kind}) differs between Challenge and Solution")
    sol_axioms = sorted(table.display[n] for n, d in S.items() if d[0] == "axiom")
    chal_axioms = sorted(table.display[n] for n, d in C.items() if d[0] == "axiom")
    bad = [a for a in sol_axioms if a not in PERMITTED]
    if bad:
        failures.append(f"unpermitted axioms in Solution closure: {bad}")
    print(f"targets: {len(targets)}; non-target Challenge declarations compared: {compared}")
    print(f"axioms in Challenge closure: {chal_axioms}")
    print(f"axioms in Solution closure: {sol_axioms}")
    if failures:
        print("SECONDARY CHECK FAIL")
        for x in failures[:50]:
            print("  " + x)
        sys.exit(1)
    print("SECONDARY CHECK PASS: every exported Challenge declaration is structurally identical "
          "in the Solution export, all target signatures match, only permitted axioms")


if __name__ == "__main__":
    main()
