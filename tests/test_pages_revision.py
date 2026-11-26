import subprocess
import tempfile
import unittest
from unittest.mock import Mock

from scripts.pages_revision import passing_run, records, skip_reason


class PagesRevision(unittest.TestCase):
    def setUp(self):
        checkout = tempfile.TemporaryDirectory()
        self.addCleanup(checkout.cleanup)
        self.cwd = checkout.name
        self.git('init', '-q', '-b', 'main')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'user.email', 'test@example.test')
        self.first = self.commit('first')
        self.middle = self.commit('middle')
        self.tip = self.commit('tip')

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.cwd, text=True).strip()

    def commit(self, name):
        self.git('commit', '-q', '--allow-empty', '-m', name)
        return self.git('rev-parse', 'HEAD')

    def test_pending_pushes_do_not_starve_a_passing_ancestor(self):
        lookup = Mock(return_value=None)
        self.assertIsNone(skip_reason(self.first, self.tip, lookup, self.cwd))
        self.assertEqual({call.args[0] for call in lookup.call_args_list}, {self.middle, self.tip})
        lookup.reset_mock()
        self.assertIsNone(skip_reason(self.tip, self.tip, lookup, self.cwd))
        lookup.assert_not_called()

    def test_out_of_order_finishes_skip_only_the_older_artifact(self):
        verified = {self.middle: 22}.get
        self.assertIn('run 22', skip_reason(self.first, self.tip, verified, self.cwd))
        self.assertIsNone(skip_reason(self.middle, self.tip, verified, self.cwd))

    def test_force_push_excludes_removed_revisions_and_their_runs(self):
        self.git('checkout', '-q', '-b', 'replacement', self.first)
        replacement = self.commit('new history')
        lookup = Mock(side_effect={self.tip: 33}.get)
        self.assertIn('no longer on main', skip_reason(self.tip, replacement, lookup, self.cwd))
        lookup.assert_not_called()
        self.assertIsNone(skip_reason(self.first, replacement, lookup, self.cwd))
        lookup.assert_called_once_with(replacement)

    def test_rejoined_force_pushed_history_cannot_overwrite_a_verified_sibling(self):
        self.git('checkout', '-q', '-b', 'replacement', self.first)
        sibling = self.commit('replacement deployed to main')
        self.git('merge', '-q', '--no-ff', '-m', 'rejoin both lines', self.tip)
        merge = self.git('rev-parse', 'HEAD')
        self.assertIn('run 31', skip_reason(self.tip, merge, {sibling: 31}.get, self.cwd))
        self.assertIsNone(skip_reason(self.tip, merge, {}.get, self.cwd))

    def test_trusted_verify_job_can_pass_while_publish_is_pending_or_retrying(self):
        sha = self.tip
        template = dict(head_sha=sha, event='push', head_branch='main')
        # The Actions run is currently in progress. Its earlier attempt passed verify.
        runs = [dict(template, id=1, event='pull_request'), dict(template, id=2, head_branch='codex/a'),
                dict(template, id=3, head_sha=self.first), dict(template, id=4, status='in_progress')]
        rpages = [dict(total_count=4, workflow_runs=runs[:2]), dict(total_count=4, workflow_runs=runs[2:])]
        good = dict(id=10, head_sha=sha, run_id=4, name='verify', status='completed', conclusion='success')
        jobs = [dict(good, id=11, status='in_progress', conclusion=None), dict(good, id=12, name='publish'), good]
        jpages = [dict(total_count=3, jobs=jobs[:2]), dict(total_count=3, jobs=jobs[2:])]
        fetch = Mock(side_effect=[rpages, jpages])
        self.assertEqual(passing_run('org/test', sha, fetch), 4)
        self.assertEqual(fetch.call_args_list[0].args[0], f'repos/org/test/actions/workflows/verify.yml/runs?head_sha={sha}&per_page=100')
        self.assertEqual(fetch.call_args_list[1].args[0], 'repos/org/test/actions/runs/4/jobs?filter=all&per_page=100')
        jobs[-1]['conclusion'] = 'failure'
        self.assertIsNone(passing_run('org/test', sha, Mock(side_effect=[rpages, jpages])))

    def test_dispatch_needs_branch_only_upload(self):
        run = dict(id=2, event='workflow_dispatch', head_branch='main', head_sha=self.tip)
        job = dict(id=8, head_sha=self.tip, run_id=2, name='verify', status='completed', conclusion='success')
        for name in ('Run actions/upload-pages-artifact@123', 'Upload verified main artifact'):
            for result in ('skipped', 'success'):
                job['steps'] = [dict(name=name, conclusion=result)]
                fetch = Mock(side_effect=[[dict(total_count=1, workflow_runs=[run])],
                                          [dict(total_count=1, jobs=[job])]])
                self.assertEqual(passing_run('org/test', self.tip, fetch), 2 if result=='success' else None)

    def test_saturated_filtered_search_falls_back_without_an_age_cutoff(self):
        run = dict(id=1, event='push', head_branch='main', head_sha=self.tip)
        job = dict(id=2, head_sha=self.tip, run_id=1, name='verify', status='completed', conclusion='success')
        fetch = Mock(side_effect=[[dict(total_count=1000, workflow_runs=[])],
                                  [dict(total_count=1, workflow_runs=[run])], [dict(total_count=1, jobs=[job])]])
        self.assertEqual(passing_run('org/test', self.tip, fetch), 1)
        self.assertEqual(fetch.call_args_list[1].args[0], 'repos/org/test/actions/workflows/verify.yml/runs?per_page=100')

    def test_incomplete_pagination_and_api_errors_abort(self):
        for pages in ([], [dict(total_count=2, jobs=[dict(id=1)])],
                      [dict(total_count=2, jobs=[dict(id=1), dict(id=1)])]):
            with self.assertRaises(ValueError):
                records(pages, 'jobs')
        with self.assertRaises(subprocess.CalledProcessError):
            skip_reason(self.first, self.tip, Mock(side_effect=subprocess.CalledProcessError(1, 'gh')), self.cwd)
