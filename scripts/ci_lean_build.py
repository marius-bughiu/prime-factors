"""Remove retired or untraced project modules before an incremental Lake build."""

from collections import defaultdict
from pathlib import Path


def prune_restored_modules(root):
    build = root / '.lake' / 'build'
    library = build / 'lib' / 'lean'
    artifacts = defaultdict(list)
    for directory in (library, build / 'ir'):
        for path in directory.rglob('*'):
            name, _, suffix = path.name.partition('.')
            if suffix.split('.')[0] in {'olean', 'ilean', 'trace', 'c', 'bc'} and path.is_file():
                module = path.relative_to(directory).with_name(name)
                artifacts[module].append(path)

    removed = 0
    for module, files in artifacts.items():
        # With no .trace, Lake 4.19 may compare mtimes. Removing the artifacts
        # forces a real build. Retired modules must also disappear from LEAN_PATH.
        if (root / module.with_suffix('.lean')).is_file() and (library / module.with_suffix('.trace')).is_file():
            continue
        for path in files:
            path.unlink()
        removed += 1
    return removed


if __name__ == '__main__':
    removed = prune_restored_modules(Path(__file__).resolve().parents[1])
    print(f'Removed cached artifacts for {removed} retired or untraced Lean modules')
