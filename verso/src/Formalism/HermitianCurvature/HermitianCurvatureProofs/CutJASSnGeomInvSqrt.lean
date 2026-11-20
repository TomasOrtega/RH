import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def phiS (c t : ℝ) : ℝ := sc c t * (Real.sqrt t)⁻¹

def PhiS (c : ℝ) (w : ℂ) : ℂ := ((phiS c w.re : ℝ) : ℂ)

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `t`. Distinguish the cases in `ht : c / 8 < t`. Establish `h1 : ContDiff ℝ ∞ (sc c)`. Unfold `sc`.

Conclude with `Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)`. Establish `hpos : 0 < t` using `by linarith`. Establish `h2 : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.sqrt y)⁻¹) t` using `(Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'`. Conclude with `h1.contDiffAt.mul h2`. Establish `hev : phiS c =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ)` using `by filter_upwards [Iio_mem_nhds (show t < c / 4 by linarith)] with y hy`.

Establish `hy' : y < c / 4` using `hy`. Establish `h0 : (y - c / 4) / (c / 4) ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)`. Simplify using `[phiS, sc, Real.smoothTransition.zero_of_nonpos h0]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq hev`.
-/
lemma phiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (phiS c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : c / 8 < t
  · have h1 : ContDiff ℝ ∞ (sc c) := by
      unfold sc
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    have hpos : 0 < t := by linarith
    have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.sqrt y)⁻¹) t :=
      (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
    exact h1.contDiffAt.mul h2
  · have hev : phiS c =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show t < c / 4 by linarith)] with y hy
      have hy' : y < c / 4 := hy
      have h0 : (y - c / 4) / (c / 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      simp [phiS, sc, Real.smoothTransition.zero_of_nonpos h0]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/- English proof (translation)
Use `filter_upwards [Ioi_mem_nhds ht] with y hy`. Establish `hy' : c / 2 < y` using `hy`. Establish `hc4 : 0 < c / 4` using `by positivity`. Establish `h1 : 1 ≤ (y - c / 4) / (c / 4)`. Rewrite using `[le_div_iff₀ hc4]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy0 : 0 ≤ y` using `by linarith`. Simplify using `only [phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]`. Rewrite using `[Real.rpow_neg hy0, Real.sqrt_eq_rpow]`.
-/
lemma phiS_ev {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : c / 2 < t) :
    phiS c =ᶠ[𝓝 t] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds ht] with y hy
  have hy' : c / 2 < y := hy
  have hc4 : 0 < c / 4 := by positivity
  have h1 : 1 ≤ (y - c / 4) / (c / 4) := by
    rw [le_div_iff₀ hc4]
    linarith
  have hy0 : 0 ≤ y := by linarith
  simp only [phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]
  rw [Real.rpow_neg hy0, Real.sqrt_eq_rpow]

/- English proof (translation)
Use `⟨|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * c ^ (-(1 / 2 : ℝ) - j), fun t ht => ?_⟩` and prove the remaining obligations. Establish `hct : c / 2 < t` using `by linarith`. Establish `ht0 : 0 < t` using `by linarith`. Establish `hev` using `phiS_ev hc hct`. Rewrite using `[(hev.iteratedFDeriv ℝ j).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate]`.

Simplify using `only [Real.iter_deriv_rpow_const]`. Rewrite using `[norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]`. Establish `hj : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Establish `hq : -(1 / 2 : ℝ) - (j : ℝ) ≤ 0` using `by linarith`. Conclude with `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht hq) (abs_nonneg _)`.
-/
lemma phiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ A : ℝ, ∀ t : ℝ, c ≤ t → ‖iteratedFDeriv ℝ j (phiS c) t‖ ≤ A := by
  refine ⟨|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * c ^ (-(1 / 2 : ℝ) - j), fun t ht => ?_⟩
  have hct : c / 2 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hev := phiS_ev hc hct
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hq : -(1 / 2 : ℝ) - (j : ℝ) ≤ 0 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht hq) (abs_nonneg _)

/- English proof (translation)
Introduce `c`. Use function extensionality and compare the values at `w`. Simplify using `[PhiS]`.
-/
lemma PhiS_eq : ∀ c : ℝ, PhiS c = (Complex.ofRealCLM) ∘ (phiS c ∘ Complex.reCLM) := by
  intro c
  funext w
  simp [PhiS]

/- English proof (translation)
Rewrite using `[PhiS_eq]`. Conclude with `Complex.ofRealCLM.contDiff.comp ((phiS_cd hc).comp Complex.reCLM.contDiff)`.
-/
lemma PhiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (PhiS c) := by
  rw [PhiS_eq]
  exact Complex.ofRealCLM.contDiff.comp ((phiS_cd hc).comp Complex.reCLM.contDiff)

/- English proof (translation)
Take `⟨A, hA⟩` from `phiS_bound hc j`. Use `⟨‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖), fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw' : c ≤ w.re` using `hw`. Establish `hj : (j : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Rewrite using `[PhiS_eq]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.reCLM.iteratedFDeriv_comp_right (phiS_cd hc) w hj]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `hA _ (by simpa using hw')`.
-/
lemma PhiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ B : ℝ, ∀ w ∈ {w : ℂ | c ≤ w.re}, ‖iteratedFDeriv ℝ j (PhiS c) w‖ ≤ B := by
  obtain ⟨A, hA⟩ := phiS_bound hc j
  refine ⟨‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖), fun w hw => ?_⟩
  have hw' : c ≤ w.re := hw
  have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [PhiS_eq]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (phiS c ∘ Complex.reCLM)) w‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (phiS c ∘ Complex.reCLM) w‖ :=
        Complex.ofRealCLM.norm_iteratedFDeriv_comp_left ((phiS_cd hc).comp Complex.reCLM.contDiff).contDiffAt hj
    _ ≤ ‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖) := by
        gcongr
        rw [Complex.reCLM.iteratedFDeriv_comp_right (phiS_cd hc) w hj]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        gcongr
        exact hA _ (by simpa using hw')

/- English proof (translation)
Introduce `k r d P hP S hSG c hc hSc n`. Take `⟨hPcd, -⟩` from `poly_adm (n := n) hP`. Take `⟨M, hM⟩` from `poly_H hP n`. Establish `hU : UBL (fun g => PhiS c (P g)) S n 0 d` using `ubl_fdb P hPcd S hSG {w : ℂ | c ≤ w.re} hSc d n M hM (PhiS c) (PhiS_cd hc) (PhiS_bound hc)`. Use `ubl_congr (V := P ⁻¹' {w : ℂ | c / 2 < w.re}) ?_ ?_ hSG ?_ hU` and prove the remaining obligations.

Conclude with `(isOpen_lt continuous_const Complex.continuous_re).preimage hPcd.continuous`. Introduce `g hg`. Establish `h` using `hSc g hg`. Use `show c / 2 < (P g).re`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `g _ hg`. Establish `hg' : c / 2 < (P g).re` using `hg`. Establish `hc4 : 0 < c / 4` using `by positivity`. Establish `h1 : 1 ≤ ((P g).re - c / 4) / (c / 4)`. Rewrite using `[le_div_iff₀ hc4]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ) = PhiS c (P g)`. Rewrite using `[PhiS, phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]`.
-/
theorem unipotent_inverse_sqrt_bound : UBLInvSqrt := by
  intro k r d P hP S hSG c hc hSc n
  obtain ⟨hPcd, -⟩ := poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hU : UBL (fun g => PhiS c (P g)) S n 0 d :=
    ubl_fdb P hPcd S hSG {w : ℂ | c ≤ w.re} hSc d n M hM (PhiS c) (PhiS_cd hc) (PhiS_bound hc)
  refine ubl_congr (V := P ⁻¹' {w : ℂ | c / 2 < w.re}) ?_ ?_ hSG ?_ hU
  · exact (isOpen_lt continuous_const Complex.continuous_re).preimage hPcd.continuous
  · intro g hg
    have h := hSc g hg
    show c / 2 < (P g).re
    linarith
  · intro g _ hg
    have hg' : c / 2 < (P g).re := hg
    have hc4 : 0 < c / 4 := by positivity
    have h1 : 1 ≤ ((P g).re - c / 4) / (c / 4) := by
      rw [le_div_iff₀ hc4]
      linarith
    show (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ) = PhiS c (P g)
    rw [PhiS, phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
