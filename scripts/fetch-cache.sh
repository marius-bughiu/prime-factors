#!/bin/sh
# Fetch only the compiled Mathlib modules used by the library and proof generator.
set -eu
export MATHLIB_NO_CACHE_ON_UPDATE=1
exec lake exe cache get \
  Mathlib.Data.Nat.Factors Mathlib.Data.Nat.Sqrt Mathlib.Data.ZMod.Units \
  Mathlib.FieldTheory.Finite.Basic Mathlib.NumberTheory.ArithmeticFunction \
  Mathlib.NumberTheory.LucasPrimality Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum.NatSqrt Mathlib.Tactic.NormNum.Prime \
  Mathlib.Tactic.ReduceModChar Mathlib.Tactic.Ring
