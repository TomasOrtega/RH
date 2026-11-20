import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula

noncomputable section

namespace GlobalTheory.CurveSigmaAlg

open NumberField Formalism.BasicNotions GlobalTheory.IsogConst

/- English proof (translation)
Establish `hδ0 : δ ≠ 0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ`. Take `⟨-, hCM⟩` from `GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0`. Introduce `ω hω`. Establish `h1` using `hCM ω (by rw [← hL]; exact hω)`. Rewrite `h1` using `[← hL]`.

Establish `e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d`. Unfold `Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h1`.
-/
theorem hasCMBy_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨-, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  intro ω hω
  have h1 := hCM ω (by rw [← hL]; exact hω)
  rw [← hL] at h1
  have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
  rw [e]; exact h1

/- English proof (translation)
Introduce `hInv D cc δ hcc hδ L hL`. Take `⟨h2, h3⟩` from `hInv D cc δ hcc hδ L hL`. Establish `hcm` using `hasCMBy_curve D cc δ hcc hδ L hL`. Establish `hd0 : 0 < D.host.d` using `(D.host.hyp.2.1 : D.host.d.Prime).pos`. Take `⟨S, -, -, hIso, -⟩` from `Formalism.L2.Th1.F.hasCMByIsogeny D.host.d L hcm (-1) 2 (by simp) hd0`.

Establish `hαsq` using `alpha_sq D.host.d`. Establish `hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ Formalism.MainNotions.TaylorLogMetric.Qbar` using `qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))`. Establish `hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0`. Introduce `h0`. Rewrite `hαsq` using `[h0]`.

Establish `: (D.host.d : ℂ) = 0` using `by linear_combination hαsq`. Establish `: D.host.d = 0` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Establish `he : InQ (Formalism.L2.Th1.F.pSeries L)`. Introduce `k`.

Rewrite using `[Formalism.L2.KerInert.AlgP.pSeries_eq_map Formalism.MainNotions.TaylorLogMetric.Qbar L h2 h3, PowerSeries.coeff_map]`. Conclude with `SetLike.coe_mem _`. Establish `hc` using `algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso`. Rewrite `hc` using `[hαsq]`. Establish `hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ)` using `by push_cast; ring`.

Rewrite `hc` using `[hN]`. Establish `hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0`. Conclude with `(by omega : Fintype.card S + 1 + D.host.d ≠ 0)` after adjusting the coercions. Establish `e : Formalism.L2.Th1.F.s2 L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ * (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 L)`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hN0, one_mul]`.

Rewrite using `[e]`. Conclude with `mul_mem (inv_mem (natCast_mem _ _)) hc`.
-/
theorem secondEisensteinAlgebraic_of_invAlg : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  intro hInv D cc δ hcc hδ L hL
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d L hcm (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map Formalism.MainNotions.TaylorLogMetric.Qbar L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

end GlobalTheory.CurveSigmaAlg
