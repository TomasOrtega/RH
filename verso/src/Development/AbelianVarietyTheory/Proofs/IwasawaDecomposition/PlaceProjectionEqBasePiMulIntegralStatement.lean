import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionEqBasePiMulIntegral
import Mathlib
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPlaceProjectionEqBasePiMulIntegral.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.placeProjection_eq_basePi_mul_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  first | exact @GlobalTheory.Mem.Col2.prV_eq_pi_mul | exact GlobalTheory.Mem.Col2.prV_eq_pi_mul | (intros; apply GlobalTheory.Mem.Col2.prV_eq_pi_mul <;> assumption)
