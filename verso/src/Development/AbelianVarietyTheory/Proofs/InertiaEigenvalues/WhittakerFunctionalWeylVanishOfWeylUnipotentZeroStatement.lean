import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWhittakerFunctionalWeylVanishOfWeylUnipotentZero.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.lam_flip_eq_zero | exact GlobalTheory.JR.lam_flip_eq_zero | (intros; apply GlobalTheory.JR.lam_flip_eq_zero <;> assumption)
