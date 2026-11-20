import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviShiftTransposeRelation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviShiftTransposeRelation.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.levi_shift_transpose_relation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ d d₁ : ℕ)
    (W : Spc F E d) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J)
    (m : UA σ W.J), IsLevi H' t h₁ m → ∀ l : (AE F E)ˣ,
      shiftA H H' (l * Units.map (cA σ : AE F E →* AE F E) t) * (mat m)ᵀ = shiftA H H' l := by
  first | exact @GlobalTheory.ThK.LeviShift.shiftA_mul_levi | exact GlobalTheory.ThK.LeviShift.shiftA_mul_levi | (intros; apply GlobalTheory.ThK.LeviShift.shiftA_mul_levi <;> assumption)
