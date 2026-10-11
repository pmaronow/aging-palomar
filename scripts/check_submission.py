#!/usr/bin/env python3
"""Check the submission's source inventory, imports and specification boundaries."""

import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import tomllib


ROOT = Path(__file__).resolve().parents[1]
EXCLUDED = {'.git', '.lake'}
MANIFEST = 'submission/source-manifest.json'
CHALLENGE = 'Challenge'
SOLUTION = 'Solution'
TARGETS = ['SphericalAging.PalomarCompleteTheorems.exists_complete_conclusions',
           'SphericalAging.PalomarStationarityCertificate.proposition5_7']
COMPILED_SUFFIXES = {'.a', '.bc', '.dll', '.dylib', '.ilean', '.ir', '.o', '.obj',
                     '.olean', '.so', '.trace', '.private', '.server', '.pyc'}
LICENSE_NAME = re.compile(r'^(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?$', re.I)


def mask(text):
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('Unclosed Lean block comment')
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('Unclosed Lean string')
        else:
            i += 1
            continue
        for j in range(start, min(i, len(out))):
            if out[j] != '\n':
                out[j] = ' '
    return ''.join(out)


def files():
    result = {}
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        dirs[:] = [name for name in dirs if name not in EXCLUDED]
        for name in dirs:
            if (Path(directory) / name).is_symlink():
                raise RuntimeError(('Source directory symlink', str(Path(directory) / name)))
        for name in names:
            path = Path(directory) / name
            if path.is_symlink() or not path.is_file():
                raise RuntimeError(('Nonregular submitted file', str(path)))
            result[path.relative_to(ROOT).as_posix()] = path
    return result


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise RuntimeError(('Duplicate JSON key', key))
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_bytes().decode('utf-8'), object_pairs_hook=unique_object)


def physical_lines(text):
    return text.count('\n') + int(bool(text) and not text.endswith('\n'))


def has_module_header(text):
    """Reject module documentation before the header; full Lean parsing is separate."""
    i = 0
    while i < len(text):
        if text[i] in ' \r\n':
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i + 2)
            i = len(text) if end < 0 else end + 1
        elif text.startswith('/-', i) and not text.startswith(('/--', '/-!'), i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                return False
        else:
            return re.match(r'module\b', text[i:]) is not None
    return False


def check_project_files(inventory):
    required = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                'formalization.yaml', 'comparator.json', 'Challenge.lean', 'Solution.lean'}
    if not required <= set(inventory) or 'lakefile.lean' in inventory:
        raise RuntimeError('The standard project needs its committed root source/configuration files')
    if sum(path.stat().st_size for path in inventory.values()) > 500 * 1024 * 1024:
        raise RuntimeError('Submitted source exceeds the Palomar 500 MiB cap')
    for name, path in inventory.items():
        if path.suffix in COMPILED_SUFFIXES:
            raise RuntimeError(('Submitted generated/compiled artifact', name))
        with path.open('rb') as stream:
            if stream.read(80).startswith(b'version https://git-lfs.github.com/spec/v1\n'):
                raise RuntimeError(('Git LFS pointer', name))
    for name, cap in [('lakefile.toml', 1024 * 1024), ('comparator.json', 1024 * 1024),
                      ('formalization.yaml', 256 * 1024)]:
        if inventory[name].stat().st_size > cap:
            raise RuntimeError(('Palomar file byte limit', name))
        inventory[name].read_bytes().decode('utf-8')
    license_files = [name for name in inventory if '/' not in name and LICENSE_NAME.fullmatch(name)]
    if len(license_files) != 1:
        raise RuntimeError('Exactly one conventional root licence file is required')
    licence = inventory[license_files[0]]
    if not 0 < licence.stat().st_size <= 1024 * 1024 or not licence.read_bytes().decode('utf-8').strip():
        raise RuntimeError('The root licence must be nonempty UTF-8 and at most 1 MiB')
    lake = tomllib.loads(inventory['lakefile.toml'].read_bytes().decode('utf-8'))
    if not {CHALLENGE, SOLUTION} <= {row['name'] for row in lake.get('lean_lib', [])}:
        raise RuntimeError('Lake must register the root Challenge and Solution libraries')
    if inventory['lean-toolchain'].read_bytes().decode('utf-8').strip() != 'leanprover/lean4:v4.35.0-rc2':
        raise RuntimeError('The submitted toolchain pin changed')
    manifest = read_json(inventory['lake-manifest.json'])
    packages = manifest.get('packages')
    if not isinstance(packages, list) or len({row['name'] for row in packages}) != len(packages):
        raise RuntimeError('Lake dependency packages must be a unique list')
    for package in packages:
        if (package.get('type') != 'git'
                or re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', package.get('url', '')) is None
                or re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')) is None):
            raise RuntimeError(('Git dependency must have a credential-free GitHub URL and full commit', package.get('name')))
    mathlib = [row for row in packages if row['name'] == 'mathlib']
    if len(mathlib) != 1 or mathlib[0]['rev'] != '065356127b1dc0016f66b7283ce0ce2c4055aa55':
        raise RuntimeError('The canonical Mathlib revision changed')


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def module_name(path):
    vendor = 'vendor/hard-sphere-foundations/src/'
    return (path.removeprefix(vendor)[:-5]).replace('/', '.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-manifest', action='store_true')
    args = parser.parse_args()
    inventory = files()
    check_project_files(inventory)
    lean = {module_name(name): (name, path) for name, path in inventory.items() if name.endswith('.lean')}
    if not (len(lean) == 1921 and len(lean) == sum(name.endswith('.lean') for name in inventory)):
        raise RuntimeError(('Lean file count', len(lean)))
    if CHALLENGE not in lean or SOLUTION not in lean or any(name.startswith(('PalomarChallenges', 'PalomarSolutions')) for name in lean):
        raise RuntimeError('Only the canonical root Challenge and Solution entry modules are required')
    imports = {}
    for module, (name, path) in lean.items():
        text = path.read_bytes().decode('utf-8')
        code = mask(text)
        if not has_module_header(text):
            raise RuntimeError(('Missing module header', name))
        if not (physical_lines(text) <= 10000):
            raise RuntimeError(('Module line limit', name))
        deps = []
        in_header = True
        for line in code.splitlines():
            stripped = line.strip()
            if not stripped or stripped == 'module':
                continue
            is_import = re.match(r'^(?:(?:public|private|meta)\s+)?import\b', stripped)
            if is_import:
                if not in_header:
                    raise RuntimeError(('Import outside module header', name))
            else:
                in_header = False
        for match in re.finditer(r'^\s*(?:(?:public|private|meta)\s+)?import(?:\s+all)?\s+([^\n]+)', code, re.M):
            deps.extend(match.group(1).split())
        for dep in deps:
            if dep.split('.')[0] in {'SphericalAging', 'AbsorptionCutoff', 'BrownianMotion', 'FourPapersCommon', 'KolmogorovExtension4', 'StochasticCalculus', CHALLENGE, SOLUTION}:
                if not (dep in lean):
                    raise RuntimeError(('Missing internal import', name, dep))
        imports[module] = set(deps).intersection(lean)
        holes = re.findall(r'\b(?:sorry|admit)\b', code)
        if module == CHALLENGE:
            if imports[module] or any(dep != 'Mathlib' and not dep.startswith('Mathlib.') for dep in deps):
                raise RuntimeError(('Challenge must use independent Mathlib imports', name))
            if not (len(holes) == len(TARGETS)):
                raise RuntimeError(('Specification target placeholders', name))
            if not (physical_lines(text) <= 1000 and path.stat().st_size <= 100 * 1024):
                raise RuntimeError(('Challenge size limit', name))
        else:
            if not (not holes):
                raise RuntimeError(('Proof placeholder', name))
    def closure(start):
        found = set()
        pending = list(start)
        while pending:
            module = pending.pop()
            if module not in found:
                found.add(module)
                pending.extend(imports[module])
        return found
    proof = closure(['SphericalAging', SOLUTION])
    if not (len(closure(['SphericalAging'])) == 1918):
        raise RuntimeError('Submission check failed')
    if not (len(proof) == 1919 and proof == set(lean) - {CHALLENGE, 'Audit'}):
        raise RuntimeError('Submission check failed')
    if not (proof == imports['Audit']):
        raise RuntimeError('Audit must directly import all retained proof modules')
    claims = read_json(inventory['submission/claims.json'])
    objects = claims['objects']
    if not (len(objects) == 100 and sum(x['formalization_required'] for x in objects) == 98):
        raise RuntimeError('Submission check failed')
    if not (sum(len(x['exact_completed_declarations']) for x in objects) == 237):
        raise RuntimeError('Submission check failed')
    if len({x['label'] for x in objects}) != 100 or len({x['number'] for x in objects}) != 100:
        raise RuntimeError('Claim labels and numbers must be unique')
    if {x['number'] for x in objects if not x['formalization_required']} != {'12.2', '14.5'}:
        raise RuntimeError('Interpretive cautions must remain outside proved-result coverage')
    declarations = {name for x in objects for name in x['exact_completed_declarations']}
    if len(declarations) != 227:
        raise RuntimeError('Distinct completed-declaration count changed')
    for item in objects:
        if not (item['source'] in inventory and ('\\label{' + item['label'] + '}') in inventory[item['source']].read_text()):
            raise RuntimeError(('Manuscript label', item['label']))
        if not (bool(item['exact_completed_declarations']) == item['formalization_required']):
            raise RuntimeError(('Claim binding', item['label']))
    permitted = {'propext', 'Classical.choice', 'Quot.sound'}
    config_paths = {name for name in inventory if '/' not in name
                    and name.endswith('.json') and name.startswith('comparator')}
    if config_paths != {'comparator.json'}:
        raise RuntimeError('Exactly one comparator.json configuration is required')
    config = read_json(inventory['comparator.json'])
    required_keys = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    allowed_keys = required_keys | {'definition_names', 'enable_nanoda'}
    if not isinstance(config, dict) or not required_keys <= set(config) or not set(config) <= allowed_keys:
        raise RuntimeError('Comparator configuration has missing or unsupported keys')
    if config['challenge_module'] != CHALLENGE or config['solution_module'] != SOLUTION:
        raise RuntimeError('Comparator must select the root Challenge and Solution modules')
    if config['theorem_names'] != TARGETS or set(config['permitted_axioms']) != permitted:
        raise RuntimeError('Comparator must select both original targets and the standard axioms')
    current = {name: {'bytes': path.stat().st_size, 'sha256': digest(path)}
               for name, path in sorted(inventory.items()) if name != MANIFEST}
    if args.write_manifest:
        (ROOT / MANIFEST).write_text(json.dumps({'schema_version': 1, 'files': current}, indent=2) + '\n')
    else:
        if not (read_json(ROOT / MANIFEST)['files'] == current):
            raise RuntimeError('Source manifest mismatch')
    print(json.dumps({'passed': True, 'lean_files': len(lean), 'proof_modules': len(proof),
                      'numbered_objects': len(objects), 'mathematical_objects': 98,
                      'declaration_bindings': 237, 'palomar_entries': 1,
                      'theorem_targets': len(TARGETS), 'payload_files': len(current) + 1}))


if __name__ == '__main__':
    main()
