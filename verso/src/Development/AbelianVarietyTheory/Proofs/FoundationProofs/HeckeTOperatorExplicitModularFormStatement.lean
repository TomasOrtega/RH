import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularForm
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Hk.heckeT_modularForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeTOperatorExplicitModularForm.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_modularForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  first | exact @GlobalTheory.Hk.heckeT_modularForm | exact GlobalTheory.Hk.heckeT_modularForm | (intros; apply GlobalTheory.Hk.heckeT_modularForm <;> assumption)
