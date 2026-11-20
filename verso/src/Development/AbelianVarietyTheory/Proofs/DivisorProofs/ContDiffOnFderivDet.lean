import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory.PartialDetSmooth

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem contDiff_clm_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ContDiff ℝ ∞ (fun f : E →L[ℝ] E => f.det) := by
  classical
  let b := Module.finBasis ℝ E

  have hent : ∀ i j, ContDiff ℝ ∞ (fun f : E →L[ℝ] E => b.repr (f (b j)) i) := by
    intro i j
    let L : (E →L[ℝ] E) →ₗ[ℝ] ℝ :=
      { toFun := fun f => b.repr (f (b j)) i
        map_add' := by intro f g; simp
        map_smul' := by intro c f; simp }
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have heq : (fun f : E →L[ℝ] E => f.det) = fun f =>
      ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, b.repr (f (b i)) (σ i) := by
    funext f
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Units.smul_def, zsmul_eq_mul]
    simp [LinearMap.toMatrix_apply]
  rw [heq]
  refine ContDiff.sum (fun σ _ => ?_)
  exact contDiff_const.mul (contDiff_prod (fun i _ => hent (σ i) i))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem partialDet_contDiffOn : ∀ (d : ℕ) (N : Set ((Fin d → ℂ) × (Fin d → ℂ)))
    (G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ), IsOpen N → ContDiffOn ℝ ∞ G N →
    ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
      (fderiv ℝ (fun ξ => G (p.1, ξ)) p.2).det) N := by
  intro d N G hN hG
  have hG' := (contDiffOn_infty_iff_fderiv_of_isOpen hN).1 hG
  have hcomp : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
      (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ (Fin d → ℂ) (Fin d → ℂ))) N :=
    hG'.2.clm_comp contDiffOn_const
  have hdet := (contDiff_clm_det (E := Fin d → ℂ)).comp_contDiffOn hcomp
  refine hdet.congr (fun p hp => ?_)
  have hdiff : DifferentiableAt ℝ G p := (hG'.1 p hp).differentiableAt (hN.mem_nhds hp)
  have hin : HasFDerivAt (fun ξ : Fin d → ℂ => (p.1, ξ))
      (ContinuousLinearMap.inr ℝ (Fin d → ℂ) (Fin d → ℂ)) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hch : HasFDerivAt (fun ξ => G (p.1, ξ))
      ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ (Fin d → ℂ) (Fin d → ℂ))) p.2 := by
    have := hdiff.hasFDerivAt
    exact this.comp p.2 hin
  simp only [Function.comp]
  rw [hch.fderiv]

end GlobalTheory.PartialDetSmooth
