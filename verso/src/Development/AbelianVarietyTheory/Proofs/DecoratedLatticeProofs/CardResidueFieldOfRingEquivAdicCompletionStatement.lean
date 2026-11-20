import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
import Mathlib
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocalResidue.card_residue_of_ringEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FCardResidueFieldOfRingEquivAdicCompletion.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.LocalResidue.card_residue_of_ringEquiv | exact GlobalTheory.LocalResidue.card_residue_of_ringEquiv | (intros; apply GlobalTheory.LocalResidue.card_residue_of_ringEquiv <;> assumption)
