import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsDegreeLtTwoCorrectionSimpleZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_degree_lt_two_correction_simple_zero : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A), P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧ w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  first | exact @GlobalTheory.exists_deg_lt_two_correction_simple | exact GlobalTheory.exists_deg_lt_two_correction_simple | (intros; apply GlobalTheory.exists_deg_lt_two_correction_simple <;> assumption)
