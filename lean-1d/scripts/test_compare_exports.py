"""Self-test of compare_exports.py on small synthetic exports (format 3.1.0 records).

Checks that the comparison keeps Lean's name structure (the single component "a.b" differs from
the two components a, b), and that duplicated ids and duplicated declarations are rejected.
usage: python3 -I scripts/test_compare_exports.py   (exit status 0 iff all cases behave)
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CMP = os.path.join(HERE, "compare_exports.py")
META = {"meta": {"format": {"version": "3.1.0"}}}


def base(name_records, decl_name_id, extra=()):
    recs = [META] + name_records + [
        {"il": 1, "succ": 0},
        {"ie": 0, "sort": 1},
        {"def": {"all": [decl_name_id], "hints": "abbrev", "levelParams": [],
                 "name": decl_name_id, "safety": "safe", "type": 0, "value": 0}},
        # the single target theorem T : Sort 1 := (whatever), present in both
        {"in": 90, "str": {"pre": 0, "str": "T"}},
        {"thm": {"all": [90], "levelParams": [], "name": 90, "type": 0, "value": 0}},
    ] + list(extra)
    return recs


def write(path, recs):
    with open(path, "w", encoding="utf-8") as f:
        for r in recs:
            f.write(json.dumps(r) + "\n")


def run(chal, sol, targets):
    return subprocess.run([sys.executable, "-I", "-B", CMP, chal, sol, targets],
                          capture_output=True, text=True).returncode


def main():
    ok = True
    with tempfile.TemporaryDirectory() as d:
        tg = os.path.join(d, "targets.txt")
        with open(tg, "w") as f:
            f.write("T\n")
        one = [{"in": 1, "str": {"pre": 0, "str": "a.b"}}]                  # single component
        two = [{"in": 1, "str": {"pre": 0, "str": "a"}}, {"in": 2, "str": {"pre": 1, "str": "b"}}]
        c1, c2 = os.path.join(d, "c1.ndjson"), os.path.join(d, "c2.ndjson")
        write(c1, base(one, 1))
        write(c2, base(two, 2))
        cases = [
            ("identical exports pass", c1, c1, 0),
            ("name 'a.b' (one component) vs a.b (two components) fails", c1, c2, 1),
        ]
        dup_id = os.path.join(d, "dupid.ndjson")
        write(dup_id, base(one, 1, extra=[{"ie": 0, "sort": 0}]))
        cases.append(("duplicate expression id is rejected", dup_id, c1, 1))
        dup_decl = os.path.join(d, "dupdecl.ndjson")
        write(dup_decl, base(one, 1, extra=[{"def": {"all": [1], "hints": "abbrev",
              "levelParams": [], "name": 1, "safety": "safe", "type": 0, "value": 0}}]))
        cases.append(("duplicate declaration is rejected", c1, dup_decl, 1))
        for label, chal, sol, want in cases:
            got = run(chal, sol, tg)
            good = (got == 0) == (want == 0)
            ok &= good
            print(f"{'ok  ' if good else 'FAIL'} {label} (exit {got})")
    print("SELF-TEST PASS" if ok else "SELF-TEST FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
