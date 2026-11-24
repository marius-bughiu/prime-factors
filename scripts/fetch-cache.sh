#!/bin/sh
# Fetch only the compiled Mathlib modules used by the library and proof generator.
set -eu
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake build Cache.Main
exec lake env lean --run .lake/packages/mathlib/Cache/Main.lean get \
  Mathlib.Algebra.Field.ZMod Mathlib.Data.Nat.Factors Mathlib.Data.Nat.Sqrt Mathlib.Data.ZMod.Units \
  Mathlib.Data.Nat.Dist Mathlib.NumberTheory.DiophantineApproximation.Basic \
  Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity Mathlib.NumberTheory.PrimesCongruentOne \
  Mathlib.NumberTheory.JacobiSum.Basic Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds \
  Mathlib.NumberTheory.LSeries.Nonvanishing Mathlib.Data.Nat.Squarefree Mathlib.Data.Fintype.BigOperators \
  Mathlib.FieldTheory.Finite.Basic Mathlib.NumberTheory.ArithmeticFunction \
  Mathlib.NumberTheory.LucasPrimality Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum.NatSqrt Mathlib.Tactic.NormNum.Prime \
  Mathlib.Data.Matrix.Rank Mathlib.Algebra.Polynomial.Derivative Mathlib.Data.Nat.Digits \
  Mathlib.NumberTheory.Multiplicity Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Logic.Equiv.Prod Mathlib.SetTheory.Cardinal.Finite Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.LinearCombination Mathlib.Tactic.ReduceModChar Mathlib.Tactic.Ring
