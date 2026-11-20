import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
open NumberField IsDedekindDomain
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.norm_form_mem_nhds_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FQuadraticFormIdeleValuesMemNhdsOne.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → {a : (AdeleRing (𝓞 F) F)ˣ | ∃ x y : AdeleRing (𝓞 F) F, (a : AdeleRing (𝓞 F) F) = x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
  first | exact @GlobalTheory.QNorm.norm_form_mem_nhds_one | exact GlobalTheory.QNorm.norm_form_mem_nhds_one | (intros; apply GlobalTheory.QNorm.norm_form_mem_nhds_one <;> assumption)
