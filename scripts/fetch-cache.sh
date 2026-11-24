#!/bin/sh
# Fetch only the compiled Mathlib modules used by the library and proof generator.
set -eu
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake build Cache.Main
exec lake env lean --run .lake/packages/mathlib/Cache/Main.lean get \
  Mathlib.Data.Nat.Prime.Int Mathlib.Algebra.Field.ZMod Mathlib.Data.Nat.Factors Mathlib.Data.Nat.Sqrt Mathlib.Data.ZMod.Units \
  Mathlib.Algebra.Group.Pi.Units Mathlib.GroupTheory.Index Mathlib.Data.ZMod.QuotientRing Mathlib.Data.Nat.Totient \
  Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Data.Nat.Dist Mathlib.NumberTheory.DiophantineApproximation.Basic \
  Mathlib.Algebra.GeomSum Mathlib.Data.Nat.GCD.BigOperators Mathlib.Data.Nat.Log \
  Mathlib.NumberTheory.Divisors Mathlib.NumberTheory.Primorial Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol \
  Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity Mathlib.NumberTheory.PrimesCongruentOne \
  Mathlib.NumberTheory.JacobiSum.Basic Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds Mathlib.Analysis.SpecialFunctions.Trigonometric.Series \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse Mathlib.Data.Nat.Factorization.Induction \
  Mathlib.Data.Finset.Max Mathlib.Data.Int.Interval Mathlib.Data.Int.ModEq Mathlib.Data.Real.Archimedean \
  Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Analysis.Complex.Basic Mathlib.Tactic.IntervalCases \
  Mathlib.NumberTheory.LSeries.Nonvanishing Mathlib.Data.Nat.Squarefree Mathlib.Data.Fintype.BigOperators \
  Mathlib.FieldTheory.Finite.Basic Mathlib.NumberTheory.ArithmeticFunction Mathlib.NumberTheory.Harmonic.EulerMascheroni \
  Mathlib.Data.List.Prime Mathlib.Data.Nat.Factorization.Basic Mathlib.Data.Nat.Choose.Lucas Mathlib.NumberTheory.LucasPrimality Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum.NatSqrt Mathlib.Tactic.NormNum.Prime \
  Mathlib.Data.Matrix.Rank Mathlib.Algebra.Polynomial.Roots Mathlib.Algebra.Polynomial.Derivative Mathlib.Data.Nat.Digits \
  Mathlib.Algebra.Order.Ring.Abs Mathlib.Data.Finset.SymmDiff Mathlib.Data.Finset.Powerset Mathlib.Data.Finset.Prod \
  Mathlib.Analysis.PSeries Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.Abel \
  Mathlib.LinearAlgebra.Dual.Lemmas Mathlib.NumberTheory.EulerProduct.Basic Mathlib.FieldTheory.Finiteness \
  Mathlib.NumberTheory.Multiplicity Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Algebra.BigOperators.Group.Finset.Sigma Mathlib.Logic.Equiv.Prod Mathlib.SetTheory.Cardinal.Finite Mathlib.Tactic.FieldSimp \
  Mathlib.Algebra.Quaternion Mathlib.RingTheory.Polynomial.Dickson Mathlib.Data.Finset.NatDivisors \
  Mathlib.RingTheory.PowerSeries.Derivative Mathlib.Algebra.BigOperators.NatAntidiagonal \
  Mathlib.Tactic.LinearCombination Mathlib.Tactic.ReduceModChar Mathlib.Tactic.Ring
