"""Compile external Lean clients with the binder interfaces from the original modules."""

import argparse
from collections import defaultdict
import json
from pathlib import Path
import subprocess
import tempfile


DATA = Path(__file__).resolve().parent / "pr120_interface_data" / "client_signatures.jsonl"
PRELUDE = """module
import Lean
import {target}

open Lean Elab Command

private def binderLabel (name : Name) (bi : BinderInfo) : String :=
  if bi == .instImplicit && name.hasMacroScopes && name.eraseMacroScopes == `inst then
    "<anonymous instance>"
  else toString name

private partial def interfaceOf : Expr → List String
  | .forallE n _ rest bi => (binderLabel n bi ++ "/" ++ reprStr bi) :: interfaceOf rest
  | _ => []
"""


def client(target, checks):
    source = [PRELUDE.format(target=target)]
    for name, expected in checks:
        binders = "[" + ", ".join(json.dumps(x, ensure_ascii=False) for x in expected) + "]"
        args = " ".join("x" + str(i + 1) for i in range(len(expected)))
        source.extend([f"#check @_root_.{name}", "run_cmd do",
                       f"  let actual := interfaceOf (← getConstInfo `{name}).type",
                       f'  unless actual == {binders} do throwError m!"Unexpected binders for {name}: {{actual}}"',
                       f"example : type_of% (@_root_.{name}) := by"])
        if args:
            source.append("  intro " + args)
        source.extend([f"  exact @_root_.{name} {args}".rstrip(), ""])
    return "\n".join(source)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--locations", type=Path, required=True, help="member map from prepare_pr120_interfaces.py")
    cli.add_argument("--project", type=Path, help="compile the clients against the artifacts in this Lake project")
    cli.add_argument("--emit-clients", type=Path, help="keep the generated clients in this directory")
    args = cli.parse_args()
    if not args.project and not args.emit_clients:
        cli.error("specify --project or --emit-clients")
    location = dict(row.split("\t") for row in args.locations.read_text().splitlines())
    by_member = defaultdict(list)
    for line in DATA.read_text().splitlines():
        member, name, binders = json.loads(line)
        by_member[member].append((name, binders))
    passed = failed = pending = 0
    with tempfile.TemporaryDirectory() as directory:
        clients = (args.emit_clients or Path(directory)).resolve()
        clients.mkdir(exist_ok=True, parents=True)
        for member, checks in by_member.items():
            target = location[member]
            file = clients / (member + ".lean")
            file.write_text(client(target, checks))
            if args.project:
                module = Path(*target.split(".")).with_suffix(".olean")
                if not (args.project / ".lake/build/lib/lean" / module).is_file():
                    pending += 1
                    print("PENDING", member, target, flush=True)
                    continue
                result = subprocess.run(["lake", "env", "lean", "-j1", "--root=" + str(clients), str(file)],
                                        cwd=args.project, capture_output=True, text=True)
                if result.returncode:
                    failed += 1
                    print("FAIL", member, target, "\n" + result.stdout + result.stderr, flush=True)
                else:
                    passed += 1
                    print("PASS", member, target, flush=True)
    if args.project:
        print(f"Passed {passed}, failed {failed}, pending {pending}")
    return 1 if failed else (2 if pending else 0)


if __name__ == "__main__":
    raise SystemExit(main())
