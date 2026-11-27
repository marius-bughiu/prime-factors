# Contributing

A contribution can establish an exact factorization, prove that a region can be excluded, or measure a method on a reproducible family. Small, independently reviewable changes are easiest to check.

## Responsible disclosure

If a finding looks like a major factoring breakthrough, contact a human maintainer privately and ask for review before sharing technical details. This applies to promising, partially verified findings as well as completed proofs. A practical general method for recovering two unknown 1,024-bit primes from their product is one example.

Keep the finding and anything that could reveal the method off public remotes, forks, issues, pull requests, CI, and Pages. Agree on a private way to share the evidence with the reviewers. They will coordinate disclosure with affected parties as appropriate and explicitly confirm what can be published and when.

## Submitting routine research

An issue can start with the precise claim and one example.

We welcome AI-assisted work. Each submitting contributor owns the argument, checks the generated code and explains its assumptions in the pull request. Follow the local build and audit instructions. Mathlib’s guidance on AI disclosure and Physlib’s agent instructions informed this workflow. [Mathlib contribution guide](https://leanprover-community.github.io/contribute/index.html) · [Physlib AI policy](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md)

For a new method, include an input it helps, a case it leaves unresolved, and the command that demonstrates each. When reporting a speedup, identify the baseline, account for certificate generation and verification, and report any precomputation. Cite the theorem used and describe which steps are formalized. If adapting external source, record its version, license, attribution and any redistribution requirements. The existing MIT license covers this project's original contributions. [Local workflow](AGENTS.md) · [Project license](LICENSE)
