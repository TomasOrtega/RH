import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsGeneratorMinpoly
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteFieldExistsGeneratorMinpoly.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra (ZMod l) K], ∃ (a : K) (p : (ZMod l)[X]), p.Monic ∧ Irreducible p ∧ aeval a p = 0 ∧ aeval a (derivative p) ≠ 0 ∧ (∀ y : K, ∃ q : (ZMod l)[X], aeval a q = y) ∧ Nat.card K = l ^ p.natDegree := by
  first | exact @GlobalTheory.finiteField_exists_generator_minpoly | exact GlobalTheory.finiteField_exists_generator_minpoly | (intros; apply GlobalTheory.finiteField_exists_generator_minpoly <;> assumption)
