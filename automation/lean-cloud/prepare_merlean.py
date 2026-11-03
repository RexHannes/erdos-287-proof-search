#!/usr/bin/env python3
"""Prepare the locked MerLean Heavy package without executing it or calling a model."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]

def git(*args, capture=False):
    return subprocess.run(["git", *args], check=True, text=True,
                          stdout=subprocess.PIPE if capture else None).stdout

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-only", action="store_true")
    args = parser.parse_args()
    lock = json.loads((ROOT / "automation/lean-cloud/agents.lock.json").read_text())
    tool = lock["tools"]["merlean"]
    sha = tool["commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise ValueError("MerLean must be locked to a complete Git commit.")
    if tool["repository"] != "https://github.com/MerLeanProver/MerLean.git":
        raise ValueError("Unexpected MerLean source; review it before changing this helper.")
    entry = Path(tool["entrypoint"])
    if entry.is_absolute() or ".." in entry.parts:
        raise ValueError("Unsafe package entrypoint.")
    destination = ROOT / ".lake/agent-tools" / ("merlean-" + sha[:12])
    if not args.print_only:
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            if not (destination / ".git").is_dir():
                raise ValueError("Existing destination is not the expected Git checkout.")
            head = git("-C", str(destination), "rev-parse", "HEAD", capture=True).strip()
            origin = git("-C", str(destination), "remote", "get-url", "origin", capture=True).strip()
            if head != sha or origin != tool["repository"]:
                raise ValueError("Existing checkout differs; it has been preserved.")
            if git("-C", str(destination), "status", "--porcelain", capture=True).strip():
                raise ValueError("Existing checkout has local changes; they have been preserved.")
        else:
            git("clone", "--filter=blob:none", "--no-checkout", "--depth=1",
                tool["repository"], str(destination))
            git("-C", str(destination), "fetch", "--depth=1", "origin", sha)
            git("-C", str(destination), "checkout", "--detach", sha)
        actual = git("-C", str(destination), "rev-parse", "HEAD", capture=True).strip()
        if actual != sha or not (destination / entry).is_file():
            raise ValueError("Prepared package does not match the locked entrypoint.")
    print(json.dumps({
        "commit": sha, "package_root": str(destination),
        "heavy_entrypoint": str(destination / entry),
        "state": "planned" if args.print_only else "prepared",
        "host_registration": "not performed",
        "model_calls": 0,
        "next": "Read AUTONOMOUS_FORMALISATION.md and the Heavy entrypoint; adapt to the actual host."
    }, indent=2))

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print("MERLEAN PREPARATION FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
