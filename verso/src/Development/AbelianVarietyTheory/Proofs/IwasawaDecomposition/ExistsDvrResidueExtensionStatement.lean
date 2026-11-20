import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open IsLocalRing GlobalTheory.LN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsDvrResidueExtension.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_dvr_residue_extension : ∀ {A : Type} [CommRing A] [IsLocalRing A] {L : Type} [Field L] (φ : ResidueField A →+* L), φ.Finite → CharZero (ResidueField A) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (α : A →+* W), IsLocalHom α → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ ∃ σ : L →+* ResidueField V, ∀ a : A, σ (φ (residue A a)) = residue V (f (α a)) := by
  first | exact @GlobalTheory.exists_cDvr_residue_lift | exact GlobalTheory.exists_cDvr_residue_lift | (intros; apply GlobalTheory.exists_cDvr_residue_lift <;> assumption)
