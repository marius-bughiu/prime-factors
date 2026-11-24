"""Render the GitHub Pages report from one benchmark run."""

import argparse
import json
import shutil
from html import escape
from pathlib import Path
from string import Template

ROOT = Path(__file__).resolve().parents[1]


def duration(seconds):
    if seconds < 0.01:
        return f'{seconds * 1000:.2f} ms'
    return f'{seconds:.2f} s'


def case_row(result):
    checked = result['verified']
    name = escape(result['id'])
    size = result['bits']
    status = 'Lean checked' if checked else 'Partial'
    cls = 'status' if checked else 'status partial'
    factors = ' × '.join(escape(x) for x in result['factors']) or 'None'
    evidence = (f'<a href="{escape(result["certificate"])}">Download Lean certificate</a>' if checked
                else '<span>Remaining cofactor(s)</span> <code>' + ' × '.join(map(escape, result['remaining'])) + '</code>')
    verification = duration(result['verification_seconds']) if checked else 'not run'
    if 'exclusion' in result:
        x = result['exclusion']
        evidence += (f'<p>Lean excludes every even factor gap through {int(x["max_gap"]):,}. '
                     f'<a href="{escape(x["proof"])}">Download exclusion proof</a></p>')
        verification = duration(x['verification_seconds']) + ' (replay of the prebuilt gap-exclusion theorem)'
    if result['method'] == 'subgroup':
        w = result['subgroup']
        unit = 'base' if w['bases_tested'] == 1 else 'bases'
        count = f'Subgroup search · {w["bases_tested"]} {unit} tested · inclusive limit {w["max_base"]}'
        if w['status'] == 'split':
            count += f' · witness {w["witness_base"]}'
    elif result['method'] in ('reduced-order', 'cyclotomic'):
        if result['method'] == 'cyclotomic':
            w = result['cyclotomic']
            label = f'Cyclotomic period search · exponent N^{w["degree"]} − 1'
        else:
            w = result['reduced_order']
            label = 'Reduced-order search'
        count = (f'{label} · base {w["base"]} · {escape(w["outcome"])} · '
                 f'{w["entries_per_table"]} of {w["stride"]} entries built per table · '
                 f'{w["giants_probed"]} giant probes · {w["batch_gcds"]} batch gcds')
        if result['method'] == 'cyclotomic':
            count += f' · {w["halving_gcds"]} halving gcds'
        count += f' · search {duration(result["discovery_seconds"])}'
        if checked:
            verification += f' (certificate generation and replay {duration(result["certificate_seconds"])})'
    elif result['method'] == 'modular-hyperbola':
        w = result['hyperbola']
        count = (f'Balanced-interval modular search · {w["low_classes"]:,} low residue classes'
                 f' · {w["modular_hits"]:,} candidate products · {w["euclidean_steps"]:,} Euclidean steps'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'predecessor-square':
        w = result['predecessor_square']
        count = (f'Totient square classes · {w["scales_tested"]} scales tested'
                 f' · inclusive limit {w["max_scale"]} · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'gap-stride':
        w = result['gap_stride']
        count = (f'Powers of five in the half-gap · exponent {w["exponent"]} of {w["max_exponent"]}'
                 f' · {w["per_root"]} midpoints per root · {w["square_tests"]} square tests'
                 f' · {w["lift_tests"]} modular digit tests · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'shifted':
        outcome = 'split' if result['shifted']['status'] == 'split' else 'no split'
        count = f'Shifted-square formula · {outcome} · {result["fermat_steps"]} Fermat midpoints'
    else:
        unit = 'midpoint' if result['fermat_steps'] == 1 else 'midpoints'
        count = f'Fermat pipeline · {result["fermat_steps"]} {unit} tested · budget {result["max_steps"]}'
    return f'''<details id="{name}"><summary><span class="case-title">{escape(result['description'])}</span>
<span class="numeric size">{size} bits</span><span class="{cls}">{status}</span>
<span class="numeric time">{duration(result['wall_seconds'])}</span></summary><div class="payload">
<p>{count}</p><p class="label">Input</p><code>{escape(result['n'])}</code>
<p class="label">{'Prime factors' if checked else 'Resolved portion'}</p><code>{factors}</code>
<p>Lean verification {verification}</p><div>{evidence}</div></div></details>'''


def render(out):
    data = json.loads((out / 'results.json').read_text())
    results = sorted(data['results'], key=lambda row: -row['bits'])
    biggest = max((row for row in results if row['verified']), key=lambda row: row['bits'])
    repo = 'https://github.com/' + escape(data['repository'])
    sha = escape(data['commit'])
    complete = sum(row['verified'] for row in results)
    run_link = f' · <a href="{repo}/actions/runs/{escape(data["run_id"])}">Workflow run</a>' if data['run_id'] else ''
    html = Template((ROOT / 'site/index.html').read_text()).substitute(
        repo=repo, tree=f'{repo}/blob/{sha}', commit_url=f'{repo}/commit/{sha}', sha=sha[:7],
        bits=f"{biggest['bits']:,}", largest_desc=escape(biggest['description']), largest_id=escape(biggest['id']),
        count=len(results), complete=complete, partial=len(results) - complete,
        rows='\n'.join(map(case_row, results)), cpu=escape(data['cpu']), python=escape(data['python']),
        lean=escape(data['lean']), date=escape(data['measured_at']), run_link=run_link)
    (out / 'index.html').write_text(html)
    shutil.copyfile(ROOT / 'site/style.css', out / 'style.css')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build' / 'site')
    render(parser.parse_args().out)
