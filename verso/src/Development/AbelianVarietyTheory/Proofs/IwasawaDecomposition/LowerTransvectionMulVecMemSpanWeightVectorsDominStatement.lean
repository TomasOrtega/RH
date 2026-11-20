import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLowerTransvectionMulVecMemSpanWeightVectorsDomin.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam → ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | exact GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle <;> assumption)
