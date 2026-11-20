import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula

noncomputable section

namespace GlobalTheory.ThetaZeroAlg

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
open GlobalTheory.IsogConst

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Unfold `Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omegaK_eq (d : ℕ) : Formalism.L2.Th1.CM.omegaK d = Formalism.L2.Th1.F.cmTheta 1 d := by
  unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring

/- English proof (translation)
Introduce `ω hω`. Rewrite using `[omegaK_eq]`. Conclude with `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω`.
-/
theorem hasCMBy (B : Base D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
  intro ω hω
  rw [omegaK_eq]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω

/- English proof (translation)
Establish `hL' : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ` using `by rw [← B.lat]; rfl`. Take `⟨e2, e3⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ B.L hL'`. Establish `h` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ`. Rewrite using `[← e2, ← e3]`. Conclude with `h`.
-/
theorem disc_one (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL' : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ B.L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

/- English proof (translation)
The claim follows from `(D.host.hyp.2.1 : D.host.d.Prime).squarefree`.
-/
theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

/- English proof (translation)
Use `D.host.hyp.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

/- English proof (translation)
Establish `hdisc` using `disc_one B hcc hδ`. Establish `hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv B.L)` using `GlobalTheory.ThLoc.cm1 D.host.d B.L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) (hasCMBy B)`. Establish `hjQ : Formalism.L2.Th1.CM.jInv B.L ∈ TaylorLogMetric.Qbar` using `(qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic`. Establish `hg2c : B.L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv B.L / 1728`. Unfold `Formalism.L2.Th1.CM.jInv`.

Rewrite using `[hdisc]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : B.L.g₂ ∈ TaylorLogMetric.Qbar`. Use `qbar_of_pow (n := 3) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hg2c]`.

Conclude with `div_mem hjQ (nat_mem 1728)`. Establish `h3sq : B.L.g₃ ^ 2 = (B.L.g₂ ^ 3 - 1) / 27` using `by rw [← hdisc]; ring`. Establish `h3 : B.L.g₃ ∈ TaylorLogMetric.Qbar`. Use `qbar_of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[h3sq]`.

Conclude with `div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)`. Conclude with `⟨h2, h3⟩`.
-/
theorem g₂_g₃_mem_Qbar (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ∈ TaylorLogMetric.Qbar ∧ B.L.g₃ ∈ TaylorLogMetric.Qbar := by
  have hdisc := disc_one B hcc hδ
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv B.L) := GlobalTheory.ThLoc.cm1 D.host.d B.L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) (hasCMBy B)
  have hjQ : Formalism.L2.Th1.CM.jInv B.L ∈ TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : B.L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv B.L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : B.L.g₂ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : B.L.g₃ ^ 2 = (B.L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : B.L.g₃ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

/- English proof (translation)
Take `⟨h2, h3⟩` from `g₂_g₃_mem_Qbar B hcc hδ`. Establish `hd0 : 0 < D.host.d` using `(D.host.hyp.2.1 : D.host.d.Prime).pos`. Take `⟨S, -, -, hIso, -⟩` from `Formalism.L2.Th1.F.hasCMByIsogeny D.host.d B.L (hasCMBy B) (-1) 2 (by simp) hd0`. Establish `hαsq` using `alpha_sq D.host.d`. Establish `hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ TaylorLogMetric.Qbar` using `qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))`.

Establish `hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0`. Introduce `h0`. Rewrite `hαsq` using `[h0]`. Establish `: (D.host.d : ℂ) = 0` using `by linear_combination hαsq`. Establish `: D.host.d = 0` using `by exact_mod_cast this`.

Use linear arithmetic over natural numbers and integers. Establish `he : InQ (Formalism.L2.Th1.F.pSeries B.L)`. Introduce `k`. Rewrite using `[Formalism.L2.KerInert.AlgP.pSeries_eq_map TaylorLogMetric.Qbar B.L h2 h3, PowerSeries.coeff_map]`. Conclude with `SetLike.coe_mem _`.

Establish `hc` using `algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso`. Rewrite `hc` using `[hαsq]`. Establish `hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ)` using `by push_cast; ring`. Rewrite `hc` using `[hN]`. Establish `hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0`.

Conclude with `(by omega : Fintype.card S + 1 + D.host.d ≠ 0)` after adjusting the coercions. Establish `e : Formalism.L2.Th1.F.s2 B.L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ * (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 B.L)`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hN0, one_mul]`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem (natCast_mem _ _)) hc`.
-/
theorem kernelBase_periodLattice_sigmaTwo_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Formalism.L2.Th1.F.s2 B.L ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d B.L (hasCMBy B) (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries B.L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map TaylorLogMetric.Qbar B.L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 B.L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 B.L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

/- English proof (translation)
Take `⟨h2, h3⟩` from `g₂_g₃_mem_Qbar B hcc hδ`. Use `haveI : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar := ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩`. Establish `hN : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) ∈ B.L.lattice`. Establish `e : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) = B.ω₀` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `B.omega_mem`. Establish `hx : IsAlgebraic ℚ (B.L.weierstrassP (B.ω₀ / 2))` using `(PI.GalTorsConj.W.wp_isAlgebraic B.L TaylorLogMetric.Qbar h2 h3 2 (B.ω₀ / 2) (by norm_num) hN (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)).restrictScalars ℚ`. Conclude with `mem_algebraicClosure_iff.2 hx`.
-/
theorem weierstrassP_halfPeriod_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.weierstrassP (B.ω₀ / 2) ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  haveI : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  have hN : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) ∈ B.L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) = B.ω₀ := by push_cast; ring
    rw [e]; exact B.omega_mem
  have hx : IsAlgebraic ℚ (B.L.weierstrassP (B.ω₀ / 2)) :=
    (PI.GalTorsConj.W.wp_isAlgebraic B.L TaylorLogMetric.Qbar h2 h3 2 (B.ω₀ / 2) (by norm_num) hN
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)).restrictScalars ℚ
  exact mem_algebraicClosure_iff.2 hx

/- English proof (translation)
Introduce `D cc δ B hcc hδ k`. Take `⟨h2, h3⟩` from `g₂_g₃_mem_Qbar B hcc hδ`. Establish `hc` using `Formalism.L2.KerInert.AlgP.theta_null_coefficients B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B) TaylorLogMetric.Qbar h2 h3 (kernelBase_periodLattice_sigmaTwo_algebraic B hcc hδ) (weierstrassP_halfPeriod_algebraic B hcc hδ) k`. Unfold `Formalism.L2.Th1.F.taylor0 at hc`. Rewrite `hc` using `[PowerSeries.coeff_mk]`.

Establish `hf : ((k.factorial : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`. Establish `e : iteratedDeriv k B.th0 0 = ((k.factorial : ℕ) : ℂ) * (iteratedDeriv k (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)) 0 / ((k.factorial : ℕ) : ℂ))`. Rewrite using `[mul_div_cancel₀ _ hf]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `mul_mem (natCast_mem _ _) hc`.
-/
theorem evenTheta_iteratedDeriv_zero_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ k : ℕ, iteratedDeriv k B.th0 0 ∈ TaylorLogMetric.Qbar := by
  intro D cc δ B hcc hδ k
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hc := Formalism.L2.KerInert.AlgP.theta_null_coefficients B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B) TaylorLogMetric.Qbar h2 h3
    (kernelBase_periodLattice_sigmaTwo_algebraic B hcc hδ) (weierstrassP_halfPeriod_algebraic B hcc hδ) k
  unfold Formalism.L2.Th1.F.taylor0 at hc
  rw [PowerSeries.coeff_mk] at hc
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have e : iteratedDeriv k B.th0 0 = ((k.factorial : ℕ) : ℂ) *
      (iteratedDeriv k (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)) 0 / ((k.factorial : ℕ) : ℂ)) := by
    rw [mul_div_cancel₀ _ hf]; rfl
  rw [e]
  exact mul_mem (natCast_mem _ _) hc

end GlobalTheory.ThetaZeroAlg
