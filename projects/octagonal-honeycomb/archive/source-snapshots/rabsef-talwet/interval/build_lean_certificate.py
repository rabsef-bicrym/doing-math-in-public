#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import struct
from pathlib import Path

SCALE = 1 << 60


def parse_tree(data: bytes, i: int = 0, depth: int = 0):
    if i >= len(data):
        raise ValueError("truncated tree")
    tag = data[i]
    i += 1
    if tag <= 5:
        left, i = parse_tree(data, i, depth + 1)
        right, i = parse_tree(data, i, depth + 1)
        return {
            "chars": chr(48 + tag) + left["chars"] + right["chars"],
            "nodes": 1 + left["nodes"] + right["nodes"],
            "leaves": left["leaves"] + right["leaves"],
            "positive": left["positive"] + right["positive"],
            "infeasible": left["infeasible"] + right["infeasible"],
            "maxDepth": max(left["maxDepth"], right["maxDepth"]),
            "minNumerator": min(left["minNumerator"], right["minNumerator"]),
        }, i
    if tag == 6:
        if i + 8 > len(data):
            raise ValueError("truncated positive leaf")
        n = struct.unpack_from("<q", data, i)[0]
        i += 8
        if n <= 0:
            raise ValueError(f"nonpositive leaf numerator: {n}")
        return {"chars":"6","nodes":1,"leaves":1,"positive":1,"infeasible":0,"maxDepth":depth,"minNumerator":n}, i
    if tag == 7:
        return {"chars":"7","nodes":1,"leaves":1,"positive":0,"infeasible":1,"maxDepth":depth,"minNumerator":2**63-1}, i
    raise ValueError(f"bad tree tag {tag}")


def lean_string_expr(s: str, chunk: int = 4096) -> str:
    parts = [s[i:i+chunk] for i in range(0, len(s), chunk)]
    if len(parts) == 1:
        return json.dumps(parts[0])
    return "String.join [\n" + "\n".join("  " + json.dumps(x) + "," for x in parts) + "\n]"


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--manifest", type=Path, required=True)
    p.add_argument("--summary", type=Path, required=True)
    args = p.parse_args()

    data = args.input.read_bytes()
    if data[:5] != b"OCTV2":
        raise ValueError("expected OCTV2 certificate")
    count = data[5]
    i = 6
    cases = []
    for _ in range(count):
        if i + 2 > len(data):
            raise ValueError("truncated case header")
        owner, neighbor = data[i], data[i+1]
        i += 2
        tree_start = i
        st, i = parse_tree(data, i, 0)
        case_payload = b"OCTC2" + bytes([owner, neighbor]) + data[tree_start:i]
        st.update(owner=owner, neighbor=neighbor, bytes=len(case_payload),
                  sha256=hashlib.sha256(case_payload).hexdigest(),
                  minFloat=f"{st['minNumerator']/SCALE:.17g}")
        cases.append(st)
    if i != len(data):
        raise ValueError(f"trailing bytes: {len(data)-i}")

    manifest = {
        "format":"OCTV2",
        "description":"192-bit MPFR directed-rounding replay of full-x local inequality trees",
        "rootDomain":{"thetaOverPi":[0,0.25],"ownerTurnOverPi":{"4":[0.46,0.53],"5":[0.47,0.52]},"neighborTurnOverPi":[0,0.54],"x":[0,4.10]},
        "cases":[{k:v for k,v in st.items() if k != "chars"} for st in cases],
        "combinedBytes":len(data),
        "combinedSha256":hashlib.sha256(data).hexdigest(),
        "allLeafNumeratorsPositive":all(st["minNumerator"] > 0 for st in cases),
    }
    args.manifest.write_text(json.dumps(manifest, indent=2)+"\n")

    lines = [
        "import Mathlib\n",
        "/-!\n# Imported noncrystalline interval certificate\n\nThis module kernel-checks the integrity and exhaustive binary partition structure\nof a certificate independently replayed with 192-bit directed-rounding MPFR arithmetic.\nThe transcendental interval enclosure algorithm remains an external verified-computation\ndependency; this module verifies the finite certificate imported from that computation.\n-/\n",
        "namespace NoncrystallineIntervalCertificate\n",
        "structure TreeStats where\n  nodes : Nat\n  leaves : Nat\n  positive : Nat\n  infeasible : Nat\n  maxDepth : Nat\n  deriving DecidableEq, Repr\n",
        "def combine (a b : TreeStats) : TreeStats :=\n  { nodes := 1 + a.nodes + b.nodes\n    leaves := a.leaves + b.leaves\n    positive := a.positive + b.positive\n    infeasible := a.infeasible + b.infeasible\n    maxDepth := 1 + max a.maxDepth b.maxDepth }\n",
        "def isSplit (c : Char) : Bool :=\n  c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5'\n",
        "def parseTree : Nat → List Char → Option (TreeStats × List Char)\n  | 0, _ => none\n  | _ + 1, [] => none\n  | fuel + 1, c :: rest =>\n      if isSplit c then do\n        let (a, rest₁) ← parseTree fuel rest\n        let (b, rest₂) ← parseTree fuel rest₁\n        pure (combine a b, rest₂)\n      else if c = '6' then\n        pure ({ nodes := 1, leaves := 1, positive := 1, infeasible := 0, maxDepth := 0 }, rest)\n      else if c = '7' then\n        pure ({ nodes := 1, leaves := 1, positive := 0, infeasible := 1, maxDepth := 0 }, rest)\n      else none\n",
        "def checkTree (s : String) (expected : TreeStats) : Bool :=\n  match parseTree (s.data.length + 1) s.data with\n  | some (actual, []) => actual == expected\n  | _ => false\n",
    ]
    for st in cases:
        a,b = st["owner"],st["neighbor"]
        nm = f"tree_{a}_{b}"
        lines.append(f"def {nm} : String :=\n{lean_string_expr(st['chars'])}\n")
        lines.append(f"def expected_{a}_{b} : TreeStats :=\n  {{ nodes := {st['nodes']}, leaves := {st['leaves']}, positive := {st['positive']}, infeasible := {st['infeasible']}, maxDepth := {st['maxDepth']} }}\n")
        lines.append(f"def valid_{a}_{b} : Bool := checkTree {nm} expected_{a}_{b}\n")
    lines.append("def allValid : Bool :=\n  " + " &&\n  ".join(f"valid_{a}_{b}" for a in (4,5) for b in range(4,10)) + "\n")
    lines.append("set_option maxRecDepth 1000000 in\nset_option maxHeartbeats 0 in\ntheorem imported_certificate_partition_valid : allValid = true := by\n  native_decide\n")
    for st in cases:
        a,b=st["owner"],st["neighbor"]
        lines.append(f"theorem minNumerator_{a}_{b}_positive : (0 : Int) < {st['minNumerator']} := by norm_num\n")
    lines.append(f"def combinedSha256 : String := \"{manifest['combinedSha256']}\"\n")
    lines.append("end NoncrystallineIntervalCertificate\n")
    lean = "\n".join(lines)
    args.output.write_text(lean)

    md=["# Noncrystalline interval certificate","",f"Combined SHA-256: `{manifest['combinedSha256']}`","","| Owner | Neighbor | Nodes | Leaves | Positive | Infeasible | Depth | Minimum rigorous lower bound |","|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for st in cases:
        md.append(f"| {st['owner']} | {st['neighbor']} | {st['nodes']} | {st['leaves']} | {st['positive']} | {st['infeasible']} | {st['maxDepth']} | {st['minFloat']} |")
    md += ["","Every imported leaf has a strictly positive 192-bit MPFR lower-bound numerator or is certified infeasible.","The search covers shared-edge lengths `x ∈ [0, 4.10]`."]
    args.summary.write_text("\n".join(md)+"\n")
    print(json.dumps({"leanBytes":len(lean.encode()),"combinedBytes":len(data),"combinedSha256":manifest["combinedSha256"],"allLeafNumeratorsPositive":manifest["allLeafNumeratorsPositive"]},indent=2))


if __name__ == "__main__":
    main()
