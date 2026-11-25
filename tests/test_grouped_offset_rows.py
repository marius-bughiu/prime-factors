import unittest

from experiments.grouped_offset_rows import bounded_rows, direct


class GroupedOffsetRowsTests(unittest.TestCase):
    def test_matches_individual_offsets_and_keeps_every_square(self):
        hits = 0
        for T in range(2, 33):
            for h in range(1, 2*T+1):
                limit = 7+(T*h)%97
                by_row = bounded_rows(T, h, limit, 31)
                by_offset, count = direct(T, h, limit, 31)
                self.assertEqual([by_row[k] for k in
                                  ('raw','primitive','first_axis','both_axes')], by_offset)
                hits += count
        self.assertGreater(hits, 0)

    def test_complete_local_conditions_against_square_tables(self):
        for T in range(3, 27):
            for h in range(1, 2*T+1):
                limit = 12+(3*T+h)%71
                by_row = bounded_rows(T, h, limit, None)
                by_offset, _ = direct(T, h, limit, None)
                self.assertEqual([by_row[k] for k in
                                  ('raw','primitive','first_axis','both_axes')], by_offset)

    def test_scan_uses_only_survivors_and_respects_budget(self):
        cases = [(926,7,53), (12*4062+2,13*4062+1,13), (225,4,32)]
        for T, h, limit in cases:
            counts = bounded_rows(T, h, limit, None, max_square_tests=limit)
            report = counts['search']
            if report['factor']:
                p = int(report['factor'])
                self.assertGreater(p, 1)
                self.assertLess(p, T*T+h)
                self.assertEqual((T*T+h)%p, 0)
            else:
                self.assertEqual(report['square_tests'], counts['both_axes'])
            capped = bounded_rows(T, h, limit, None, max_square_tests=1)
            self.assertLessEqual(capped['search']['square_tests'], 1)
        found = bounded_rows(12*4062+2, 13*4062+1, 13, None, max_square_tests=13)
        self.assertEqual(found['search']['offset'], 13)
        self.assertIn(int(found['search']['factor']), [36559, 64997])

    def test_first_axis_remains_available_for_wide_coordinate(self):
        T, h = 225, 4
        result = bounded_rows(T, h, 1024, 43, max_prefix=4)
        ref, _ = direct(T, h, 1024, 43)
        self.assertIsNone(result['both_axes'])
        self.assertEqual([result[k] for k in ('raw','primitive','first_axis')], ref[:3])
