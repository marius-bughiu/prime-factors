import unittest

from scripts.render_site import case_row


class ReportProvenanceTests(unittest.TestCase):
    def test_reused_certificate_retains_its_own_date_and_revision(self):
        repo = 'https://github.com/example/prime-factors'
        row = dict(id='example', method='fermat', description='Two primes', n='77', bits=7,
                   factors=['7', '11'], remaining=[], certificate='proofs/example.lean',
                   verified=True, max_steps=1, fermat_steps=1, wall_seconds=0.3,
                   verification_seconds=0.01, discovery_seconds=0.1,
                   measurement=dict(commit='a' * 40, run_id='10', measured_at='2026-11-02',
                                    cpu='test CPU', python='3.12'),
                   certificate_verification=dict(reused=True, commit='b' * 40, run_id='9',
                                                 measured_at='2026-11-01', kernel_seconds=4.0))
        report = case_row(row, repo)
        self.assertIn('Measured 2026-11-02 on test CPU', report)
        self.assertIn('Kernel checked 2026-11-01 in 4.00 s', report)
        self.assertIn(repo + '/actions/runs/9', report)
        self.assertIn(repo + '/commit/' + 'a' * 40, report)
        self.assertIn(repo + '/commit/' + 'b' * 40, report)
        del row['measurement'], row['certificate_verification']
        self.assertNotIn('certificate reused', case_row(row, repo))
