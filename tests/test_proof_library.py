import json
from html.parser import HTMLParser
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from scripts.render_site import FINDING_TYPES, ROOT, proof_library


class LibraryMarkup(HTMLParser):
    def __init__(self):
        super().__init__()
        self.cards = []
        self.buttons = {}
        self.links = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'article' and 'data-finding' in attrs:
            self.cards.append(attrs)
        elif tag == 'button':
            self.buttons[attrs['data-filter']] = attrs['aria-pressed']
        elif tag == 'a':
            self.links.append(attrs['href'])


class ProofLibraryTests(unittest.TestCase):
    def test_all_findings_visible_and_all_impact_types_available(self):
        catalog = json.loads((ROOT / 'site/findings.json').read_text())
        with TemporaryDirectory() as folder:
            library = proof_library(Path(folder), 'https://example.org/blob/test', set())
        markup = LibraryMarkup()
        markup.feed(library['finding_filters'] + library['finding_cards'])
        ids = [card['id'] for card in markup.cards]
        self.assertEqual(ids, ['finding-' + item['id'] for item in catalog])
        self.assertEqual(len(ids), len(set(ids)))
        self.assertFalse(any('hidden' in card for card in markup.cards))
        self.assertEqual(markup.buttons, {'all': 'true', **dict.fromkeys(FINDING_TYPES, 'false')})
        for item in catalog:
            with self.subTest(item=item['id']):
                self.assertIn(item['category'], FINDING_TYPES)
                self.assertTrue(all(item[field].strip() for field in ('title', 'impact', 'scope', 'detail')))
                self.assertTrue(item['sources'])
                for source in item['sources']:
                    href = source['href']
                    if not href.startswith(('#', 'proofs/')):
                        self.assertTrue((ROOT / href.split('#')[0]).is_file(), href)

    def test_evidence_matches_the_available_benchmark_artifact(self):
        with TemporaryDirectory() as folder:
            out = Path(folder)
            (out / 'proofs').mkdir()
            proof = 'proofs/intermediate-menu-exclusion-fresh-2048.lean'
            (out / proof).touch()
            library = proof_library(out, 'https://example.org/blob/test', {'fixed-window-singleton-7294033'})
        markup = LibraryMarkup()
        markup.feed(library['finding_cards'])
        self.assertIn(proof, markup.links)
        self.assertIn('#fixed-window-singleton-7294033', markup.links)
        self.assertNotIn('proofs/intermediate-menu-exclusion-crossed-2048.lean', markup.links)
        self.assertNotIn('#intermediate-totient-extra', markup.links)
