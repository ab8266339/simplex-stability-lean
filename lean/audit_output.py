"""Fail-closed parsing of Lean's #print axioms output."""
import re
from collections import Counter

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_REPORT = re.compile(
    r"'([^'\r\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
    r"|does not depend on any axioms)"
)

def check_axiom_output(stdout, expected):
    """Require exactly one recognized report for every requested declaration."""
    expected = list(expected)
    entries = [
        (name, [x.strip() for x in (body or "").split(",") if x.strip()])
        for name, body in _REPORT.findall(stdout)
    ]
    requested = Counter(expected)
    observed = Counter(name for name, _ in entries)
    expected_names = set(requested)
    observed_names = set(observed)
    missing = sorted(expected_names - observed_names)
    unexpected = sorted(observed_names - expected_names)
    duplicates = sorted(name for name, count in observed.items() if count != 1)
    duplicate_requests = sorted(name for name, count in requested.items() if count != 1)
    axioms = sorted({axiom for _, items in entries for axiom in items})
    unknown_axioms = sorted(set(axioms) - STANDARD_AXIOMS)
    passed = bool(expected) and bool(entries) and not any((
        missing, unexpected, duplicates, duplicate_requests, unknown_axioms
    )) and len(entries) == len(expected)
    return {
        "passed": passed,
        "requested_count": len(expected),
        "parsed_count": len(entries),
        "missing": missing,
        "unexpected": unexpected,
        "duplicate_reports": duplicates,
        "duplicate_requests": duplicate_requests,
        "unknown_axioms": unknown_axioms,
        "axioms": axioms,
        "reports": [{"name": name, "axioms": items} for name, items in entries],
    }
