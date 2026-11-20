import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsOverFieldIrreducibleJoin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagsOverFieldIrreducibleJoin.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.flags_over_field_irreducible_join : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (M : ι → (Spec (CommRingCat.of L)).Modules) (r : ι → ℕ), (∀ a, VB.IsVB (M a) (r a)) → ∀ φ : ∀ a, M a ≅ M a, ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (h₁ : t₁ ≫ c = 𝟙 _) (h₂ : t₂ ≫ c = 𝟙 _) (Φ : ∀ a, (Scheme.Modules.pullback c).obj (M a) ≅ (Scheme.Modules.pullback c).obj (M a)), IrreducibleSpace T ∧ (∀ a, (Scheme.Modules.pullback t₁).map (Φ a).hom = 𝟙 _) ∧ ∀ a, (Scheme.Modules.pullback t₂).map (Φ a).hom ≫ (Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a) = ((Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a)) ≫ (φ a).hom := by
  first | exact @GlobalTheory.FlagPath.exists_path_auto | exact GlobalTheory.FlagPath.exists_path_auto | (intros; apply GlobalTheory.FlagPath.exists_path_auto <;> assumption)
