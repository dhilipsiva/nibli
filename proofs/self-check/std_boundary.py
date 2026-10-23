"""Closed candidate bindings for the named stratifier's standard-library calls.

Only the reviewed declaration signatures may be filled. Bodies implement explicit
library models, never Nibli compiler functions. The hash digest is a parameter
of the stream model; collection membership does not expose physical buckets.
Native std implementations and allocation behavior are not certified here.
"""

import hashlib
import json
from pathlib import Path
import re


DIRECTORY = Path(__file__).resolve().parent
PROFILE = "stratifier-std-v1"
MODELS = ["StdStrings", "StdMaps", "StdSetsSort", "StdHash", "StdBounded"]
PROBES = {
    "stratification": ("Stratification", ["nibli_reason::rules::check_stratification"]),
    "scc_kernel": ("SccKernel", ["nibli_reason::dependency_graph::compute_sccs", "nibli_reason::rules::check_stratification"]),
}
DECLARATION = re.compile(r"^axiom\s+([A-Za-z_][A-Za-z_0-9.]*)\s*(.*?)(?=\n\s*/--|\Z)", re.M | re.S)
TYPE_BODIES = {
    "std.collections.hash.map.HashMap": "List (K × V)",
    "std.hash.random.RandomState": "NibliSelfCheck.StdHash.Digest",
    "std.collections.hash.map.Iter": "List (K × V)",
    "std.collections.hash.set.HashSet": "List T",
    "std.hash.random.DefaultHasher": "NibliSelfCheck.StdHash.State",
    "alloc.collections.btree.set.BTreeSet": "List T",
    "alloc.collections.btree.set.IntoIter": "List T",
}
FUN_BODIES = {
    "core.borrow.Borrow.Blanket.borrow": "fun value => .ok value",
    "core.slice.Slice.sort_unstable": """fun slice => do
  let sorted ← NibliSelfCheck.StdSetsSort.sort (NibliSelfCheck.StdBounded.lessEqual cmpOrdInst.cmp) slice.val
  NibliSelfCheck.StdBounded.checkedSlice sorted""",
    "std.collections.hash.map.HashMapKVRandomStateGlobal.new": ".ok []",
    "std.collections.hash.map.HashMap.get": """fun entries query =>
  NibliSelfCheck.StdMaps.lookup (fun key => do
    let borrowed ← coreborrowBorrowInst.borrow key
    corecmpEqInst1.partialEqInst.eq borrowed query) entries""",
    "std.collections.hash.map.HashMap.insert": """fun entries key value => do
  let (previous, updated) ← NibliSelfCheck.StdMaps.insert corecmpEqInst.partialEqInst.eq key value entries
  let updated ← NibliSelfCheck.StdBounded.checkedList updated
  .ok (previous, updated)""",
    "std.collections.hash.map.HashMap.Insts.CoreOpsIndexIndexShared0QV.index": """fun entries query => do
  let found ← NibliSelfCheck.StdMaps.lookup (fun key => do
    let borrowed ← coreborrowBorrowInst.borrow key
    corecmpEqInst1.partialEqInst.eq borrowed query) entries
  match found with
  | some value => .ok value
  | none => .fail .panic""",
    "SharedAHashMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter":
        "fun entries => .ok entries",
    "std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next":
        "NibliSelfCheck.StdMaps.next",
    "std.collections.hash.set.HashSetTRandomStateGlobal.new": ".ok []",
    "std.collections.hash.set.HashSet.contains": """fun entries query =>
  NibliSelfCheck.StdSetsSort.contains (fun key => do
    let borrowed ← coreborrowBorrowInst.borrow key
    corecmpEqInst1.partialEqInst.eq borrowed query) entries""",
    "std.collections.hash.set.HashSet.insert": """fun entries value => do
  let (fresh, updated) ← NibliSelfCheck.StdSetsSort.setInsert corecmpEqInst.partialEqInst.eq value entries
  let updated ← NibliSelfCheck.StdBounded.checkedList updated
  .ok (fresh, updated)""",
    "std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish": "NibliSelfCheck.StdHash.finish",
    "std.hash.random.DefaultHasher.Insts.CoreHashHasher.write": "NibliSelfCheck.StdHash.write",
    "std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher":
        "NibliSelfCheck.StdHash.build",
    "alloc.collections.btree.set.BTreeSetTGlobal.new": ".ok []",
    "alloc.collections.btree.set.BTreeSet.insert": """fun entries value => do
  let (fresh, updated) ← NibliSelfCheck.StdSetsSort.orderedSetInsert
    corecmpOrdInst.eqInst.partialEqInst.eq (NibliSelfCheck.StdBounded.lessEqual corecmpOrdInst.cmp) value entries
  let updated ← NibliSelfCheck.StdBounded.checkedList updated
  .ok (fresh, updated)""",
    "alloc.collections.btree.set.BTreeSet.len": "NibliSelfCheck.StdBounded.checkedLength",
    "alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter":
        "fun entries => .ok entries",
    "alloc.collections.btree.set.IntoIter.Insts.CoreIterTraitsIteratorIterator.next":
        "NibliSelfCheck.StdMaps.next",
    "alloc.slice.Slice.sort": """fun slice => do
  let sorted ← NibliSelfCheck.StdSetsSort.sort (NibliSelfCheck.StdBounded.lessEqual corecmpOrdInst.cmp) slice.val
  NibliSelfCheck.StdBounded.checkedSlice sorted""",
    "alloc.string.String.Insts.CoreCmpPartialEqString.eq": "NibliSelfCheck.StdStrings.equal",
    "alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp": """fun left right => do
  let order ← NibliSelfCheck.StdStrings.compareBytes left right
  .ok (some order)""",
    "alloc.string.String.Insts.CoreCmpOrd.cmp": "NibliSelfCheck.StdStrings.compareBytes",
    "alloc.string.String.push_str": "NibliSelfCheck.StdStrings.pushStr",
    "alloc.string.String.Insts.CoreCloneClone.clone": "NibliSelfCheck.StdStrings.clone",
    "alloc.string.String.Insts.CoreHashHash.hash": "NibliSelfCheck.StdHash.hashString corehashHasherInst",
    "alloc.string.String.Insts.CoreOpsDerefDerefStr.deref": "NibliSelfCheck.StdStrings.borrow",
    "alloc.string.String.Insts.CoreConvertFromShared0Str.from": "NibliSelfCheck.StdStrings.fromStr",
    "SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter":
        "fun values => .ok ⟨values.deref, 0⟩",
}


def without_comments(text):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-[\s\S]*?-/", "", text))


def inspect_template(text):
    result = {}
    header = None
    previous_end = 0
    for match in DECLARATION.finditer(text):
        name = match.group(1)
        if name in result:
            raise ValueError(f"Duplicate external declaration: {name}")
        prefix = text[previous_end:match.start()]
        attribute = re.search(r'@\[(rust_fun|rust_type)\s+"([^"]+)"\]\s*\Z', prefix)
        if attribute is None:
            raise ValueError(f"External declaration lacks its Rust identity: {name}")
        before_attribute = without_comments(prefix[:attribute.start()])
        if header is None:
            header = re.sub(r"public import [A-Z][A-Za-z0-9]*\.Types\b",
                            "public import __INPUT__.Types", before_attribute).strip()
        elif before_attribute.strip():
            raise ValueError("Unexpected code between external declarations")
        result[name] = {
            "signature": " ".join(match.group(0).split()),
            "rust_kind": attribute.group(1), "rust_pattern": attribute.group(2),
        }
        previous_end = match.end()
    if len(re.findall(r"\baxiom\b", text)) != len(result):
        raise ValueError("Unrecognized external declaration syntax")
    return header, result


def declarations(text):
    return inspect_template(text)[1]


def render(text, bodies, expected, expected_header):
    header, observed = inspect_template(text)
    if header is None or " ".join(header.split()) != " ".join(expected_header.split()):
        raise ValueError("External template header differs from the reviewed boundary")
    if observed != expected or set(bodies) != set(expected):
        raise ValueError("External declaration inventory or signature differs from the reviewed boundary")
    imports = "\n".join(f"public import {module}" for module in MODELS)
    text = text.replace("public import Aeneas\n", f"public import Aeneas\n{imports}\n", 1)
    def replace(match):
        declaration = re.sub(r"^axiom\s+", "def ", match.group(0)).rstrip()
        return declaration + " :=\n  " + bodies[match.group(1)].replace("\n", "\n  ") + "\n"
    return DECLARATION.sub(replace, text)


def install(directory, profile, probe):
    if profile != PROFILE:
        raise ValueError("Unknown standard-library boundary profile")
    expected_probe = PROBES.get(probe["name"])
    if expected_probe != (probe.get("lean_module"), probe["roots"]):
        raise ValueError("Library boundary is not approved for these extraction roots and module")
    paths = list(directory.rglob("*Template*.lean"))
    templates = {p.name: p for p in paths}
    if len(paths) != 2 or any(p.parent != directory for p in paths) or set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("Unexpected external-template files for the reviewed boundary")
    signatures = json.loads((DIRECTORY / "std_boundary_signatures.json").read_text())
    if signatures["profile"] != profile:
        raise ValueError("Library boundary signature profile differs")
    rendered = []
    for kind, bodies in (("Types", TYPE_BODIES), ("Funs", FUN_BODIES)):
        source = templates[f"{kind}External_Template.lean"]
        rendered.append((source, render(source.read_text(), bodies, signatures[kind], signatures["headers"][kind])))
    # Validate both complete inventories before writing either replacement.
    for source, text in rendered:
        source.with_name(source.name.replace("_Template", "")).write_text(text)
        source.unlink()
    return {
        "profile": profile, "models": MODELS,
        "models_installed": True,
        "signature_manifest_sha256": hashlib.sha256((DIRECTORY / "std_boundary_signatures.json").read_bytes()).hexdigest(),
        "native_std_implementation_verified": False,
        "allocation_boundary": "Element-count and string byte bounds only; concrete allocator behavior remains outside these models",
        "hash_boundary": "Parameterized byte-stream digest; collection observations use abstract equality and membership",
    }
