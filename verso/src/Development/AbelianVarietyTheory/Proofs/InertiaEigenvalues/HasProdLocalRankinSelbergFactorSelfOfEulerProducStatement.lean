import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHasProdLocalRankinSelbergFactorSelfOfEulerProduc.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  first | exact @GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | exact GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | (intros; apply GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL <;> assumption)
