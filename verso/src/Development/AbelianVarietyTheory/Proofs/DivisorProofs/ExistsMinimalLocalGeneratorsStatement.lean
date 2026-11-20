import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGenerators
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_minimal_local_generators` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMinimalLocalGenerators.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.exists_minimal_local_generators' : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime], ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧ ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by
  first | exact @GlobalTheory.exists_minimal_local_generators | exact GlobalTheory.exists_minimal_local_generators | (intros; apply GlobalTheory.exists_minimal_local_generators <;> assumption)
