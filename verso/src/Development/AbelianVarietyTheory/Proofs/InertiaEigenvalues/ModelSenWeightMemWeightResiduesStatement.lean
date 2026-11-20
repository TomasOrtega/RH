import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResidues
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Models.model_sen_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FModelSenWeightMemWeightResidues.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.model_senWeight_mem_weight_residues : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  first | exact @GlobalTheory.Models.model_sen_mem | exact GlobalTheory.Models.model_sen_mem | (intros; apply GlobalTheory.Models.model_sen_mem <;> assumption)
