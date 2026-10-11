#!/usr/bin/env python3
"""Run the official bundled Comparator with both Palomar-selected kernels.

This is a local reproducibility check, not a Palomar registration or editorial
verdict. Output and the temporary protected configuration live outside the
candidate project. The candidate files must remain byte-identical throughout.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
TARGETS = ["SphericalAging.PalomarCompleteTheorems.exists_complete_conclusions",
           "SphericalAging.PalomarStationarityCertificate.proposition5_7"]
CONFIG_KEYS = {"challenge_module", "solution_module", "theorem_names",
               "definition_names", "permitted_axioms", "enable_nanoda"}
EXCLUDED_DIRS = {".lake", ".git", "__pycache__"}


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise RuntimeError(f"Duplicate configuration key: {key}")
        result[key] = value
    return result


def snapshot(root: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for directory, directories, files in os.walk(root, followlinks=False):
        for name in directories:
            path = Path(directory) / name
            if name not in EXCLUDED_DIRS and path.is_symlink():
                raise RuntimeError(f"Submitted directory symlink is not accepted: {path}")
        directories[:] = [n for n in directories if n not in EXCLUDED_DIRS]
        for name in files:
            path = Path(directory) / name
            if path.is_symlink():
                raise RuntimeError(f"Submitted symlink is not accepted: {path}")
            if path.is_file():
                result[str(path.relative_to(root))] = sha256(path)
    return dict(sorted(result.items()))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--config", type=Path,
                        help="Comparator configuration; default comparator.json in the project")
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--toolchain", type=Path,
                        help="Pinned Lean installation prefix; default resolved from lean on PATH")
    args = parser.parse_args()
    project = args.project.resolve()
    config_path = args.config.resolve() if args.config else project / "comparator.json"
    report_path = args.report.resolve()
    toolchain = (args.toolchain.resolve() if args.toolchain else
                 Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()).resolve())
    if report_path.is_relative_to(project):
        raise RuntimeError("The report must be outside the candidate project")
    report_path.parent.mkdir(parents=True, exist_ok=True)
    if (not config_path.is_relative_to(project) or config_path.is_symlink()
            or not config_path.is_file() or config_path.stat().st_size > 1024 * 1024):
        raise RuntimeError("The submitted configuration must be a regular project JSON file at most 1 MiB")
    config = json.loads(config_path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    if not isinstance(config, dict) or not set(config) <= CONFIG_KEYS:
        raise RuntimeError("Submitted config contains unsupported Palomar keys")
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    if not required <= set(config):
        raise RuntimeError("Submitted config omits a required key")
    if (config["challenge_module"] != "Challenge" or config["solution_module"] != "Solution"
            or config["theorem_names"] != TARGETS
            or not isinstance(config["permitted_axioms"], list)
            or not set(config["permitted_axioms"]) <= STANDARD_AXIOMS):
        raise RuntimeError("Invalid target or axiom policy")
    if not isinstance(config.get("definition_names", []), list) or config.get("definition_names", []):
        raise RuntimeError("This entry compares the two original theorems without additional definition targets")
    bin_dir = toolchain / "bin"
    binaries = ["lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]
    for binary in binaries:
        if not os.access(bin_dir / binary, os.X_OK):
            raise RuntimeError(f"Required trusted tool missing: {binary}")
    expected_toolchain = (project / "lean-toolchain").read_text().strip()
    lean_version = subprocess.check_output([str(bin_dir / "lean"), "--version"], text=True).strip()
    expected_version = expected_toolchain.removeprefix("leanprover/lean4:v")
    if f"version {expected_version}," not in lean_version:
        raise RuntimeError(f"Toolchain mismatch: {expected_toolchain} / {lean_version}")
    before = snapshot(project)
    # enable_nanoda is deliberately non-authoritative in actual Palomar intake.
    # Both independently implemented kernels are selected here by this runner.
    config.pop("enable_nanoda", None)
    config["external_kernels"] = {
        "nanoda": [str(bin_dir / "nanoda_bin")],
        "con-ron": [str(bin_dir / "con-ron"), "--jobs=2"],
    }
    log_path = report_path.with_suffix(".log")
    env = os.environ.copy()
    env["PATH"] = str(bin_dir) + os.pathsep + env.get("PATH", "")
    started = time.time()
    with tempfile.TemporaryDirectory(prefix="protected-comparator-", dir=report_path.parent) as tmp:
        protected = Path(tmp) / "comparator.json"
        protected.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
        os.chmod(protected, 0o444)
        command = [str(bin_dir / "lake"), "comparator", "--config", str(protected)]
        with log_path.open("w", encoding="utf-8") as log:
            process = subprocess.run(command, cwd=project, env=env,
                                     stdout=log, stderr=subprocess.STDOUT)
    after = snapshot(project)
    text = log_path.read_text(encoding="utf-8")
    kernel_acceptance = {name: f"{name} kernel accepts the solution" in text
                         for name in ("Lean default", "nanoda", "con-ron")}
    accepted = (process.returncode == 0 and all(kernel_acceptance.values())
                and "Your solution is okay!" in text and before == after)
    report = {
        "scope": "Local bundled Comparator check; no registry registration or editorial verdict",
        "command": command,
        "project": str(project),
        "config_path": str(config_path),
        "submitted_config_sha256": sha256(config_path),
        "challenge_module": config["challenge_module"],
        "solution_module": config["solution_module"],
        "theorem_names": config["theorem_names"],
        "definition_names": config.get("definition_names", []),
        "permitted_axioms": config["permitted_axioms"],
        "protected_config": config,
        "lean_version": lean_version,
        "tools": {n: {"path": str(bin_dir / n), "sha256": sha256(bin_dir / n)}
                  for n in binaries},
        "exit_code": process.returncode,
        "elapsed_seconds": round(time.time() - started, 3),
        "kernel_acceptance": kernel_acceptance,
        "source_unchanged": before == after,
        "source_files": len(before),
        "source_snapshot_sha256": hashlib.sha256(json.dumps(before, sort_keys=True,
                                                            separators=(",", ":")).encode()).hexdigest(),
        "source_sha256": before,
        "log_path": str(log_path),
        "log_sha256": sha256(log_path),
        "accepted": accepted,
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"accepted": accepted,
                      "exit_code": process.returncode,
                      "elapsed_seconds": report["elapsed_seconds"],
                      "report": str(report_path)}))
    return 0 if accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
