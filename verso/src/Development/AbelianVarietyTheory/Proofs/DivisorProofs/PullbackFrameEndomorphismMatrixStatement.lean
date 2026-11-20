import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFrameEndomorphismMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackFrameEndomorphismMatrix.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.pullback_frame_endomorphism_matrix : ∀ (X T : Scheme.{0}) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) (F : X.Modules) (κ : Type) [Fintype κ] (e : κ → Γ(F, ⊤)), VB.IsFrame e → ∀ (Φ : (Scheme.Modules.pullback c).obj F ⟶ (Scheme.Modules.pullback c).obj F) (B : Matrix κ κ Γ(T, ⊤)), (∀ i, Φ.app ⊤ (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) = ∑ j, B j i • QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j)) → ∀ (ψ : F ⟶ F), (∀ i, ψ.app ⊤ (e i) = ∑ j, t.appTop (B j i) • e j) → (Scheme.Modules.pullback t).map Φ ≫ (Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F = ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F) ≫ ψ := by
  first | exact @GlobalTheory.SectionPull.pullback_map_comp_canonical | exact GlobalTheory.SectionPull.pullback_map_comp_canonical | (intros; apply GlobalTheory.SectionPull.pullback_map_comp_canonical <;> assumption)
