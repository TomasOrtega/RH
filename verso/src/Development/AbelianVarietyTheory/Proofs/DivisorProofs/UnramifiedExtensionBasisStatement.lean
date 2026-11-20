import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedExtensionBasis.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.unramified_extension_basis : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ (ζ : Qr p r), IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1) → ∀ x : KQ p K r, ∃ c : Fin r → K, x = ∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) := by
  first | exact @GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow | exact GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow | (intros; apply GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow <;> assumption)
