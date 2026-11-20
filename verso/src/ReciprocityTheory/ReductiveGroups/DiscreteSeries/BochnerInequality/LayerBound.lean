import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BochIneq

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LayerBound

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

/- English proof (translation)
Establish `hVfd : FiniteDimensional ℂ V` using `hV.1`. Establish `hVk : IsKStableSub ε E V` using `hV.2.1`. Take `⟨P, hP, hP0, hPμ, hPperp⟩` from `lift_layer hE hU hVfd hVk hw hperp hμ hw0`. Use `⟨khw_big_weight hE hV hP hP0 hPμ, ?_⟩` and prove the remaining obligations. Establish `hposition : ∀ i κ, slice i κ P ∈ Wp ε E V`.

Introduce `i`. Use `position_perp hE hU hV hmono hh hbig i hP ?_` and prove the remaining obligations. Introduce `F hF hFm`. Conclude with `hPperp F hF (phi_Wm_position hE hU hV hc hmono hh hbig i hF hFm)`. Establish `hB` using `bochner_ineq hE hU hV hmono hh hbig hP hposition`.

Establish `hcas : casimirK ε (bAct E (k + 1)) P = ((casValK ε μ : ℝ) : ℂ) • P` using `casimirK_khwVec ε (bAct_isGlRep hE (k + 1)) hPμ`. Establish `hre : RCLike.re (inner ℂ (((casValK ε μ : ℝ) : ℂ) • P) P) = casValK ε μ * ‖P‖ ^ 2` using `by first`. Consider the case `(rw [inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]; done)`. Consider the case `(rw [inner_smul_real_left, RCLike.smul_re, inner_self_eq_norm_sq, smul_eq_mul]; done)`. Consider the case `(simp [inner_smul_left, inner_self_eq_norm_sq_to_K]; done)`.

Consider the case `(simp [inner_smul_left, inner_self_eq_norm_sq_to_K]; ring)`. Rewrite `hB` using `[hcas, hre]`. Establish `hpos : 0 < ‖P‖ ^ 2`. Use `norm_pos_iff.mpr hP0` as an intermediate fact. Check the signs of the components of the expression.

Establish `hle` using `le_of_mul_le_mul_right hB hpos`. Move the coercions through the operations in `at hle`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem khw_layer_succ_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) (k : ℕ) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ layer ε E V (k + 1)) (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0)
    (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) :
    IsNCSum ε (k + 1) (μ - lowK ε lam) ∧
      casValK ε (lowK ε lam) + 2 * ((k : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  have hVfd : FiniteDimensional ℂ V := hV.1
  have hVk : IsKStableSub ε E V := hV.2.1

  obtain ⟨P, hP, hP0, hPμ, hPperp⟩ := lift_layer hE hU hVfd hVk hw hperp hμ hw0
  refine ⟨khw_big_weight hE hV hP hP0 hPμ, ?_⟩

  have hposition : ∀ i κ, slice i κ P ∈ Wp ε E V := by
    intro i
    refine position_perp hE hU hV hmono hh hbig i hP ?_
    intro F hF hFm
    exact hPperp F hF (phi_Wm_position hE hU hV hc hmono hh hbig i hF hFm)
  have hB := bochner_ineq hE hU hV hmono hh hbig hP hposition
  have hcas : casimirK ε (bAct E (k + 1)) P = ((casValK ε μ : ℝ) : ℂ) • P :=
    casimirK_khwVec ε (bAct_isGlRep hE (k + 1)) hPμ
  have hre : RCLike.re (inner ℂ (((casValK ε μ : ℝ) : ℂ) • P) P) = casValK ε μ * ‖P‖ ^ 2 := by
    first
    | (rw [inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex, Complex.re_ofReal_mul,
          ← RCLike.re_to_complex, inner_self_eq_norm_sq]; done)
    | (rw [inner_smul_real_left, RCLike.smul_re, inner_self_eq_norm_sq, smul_eq_mul]; done)
    | (simp [inner_smul_left, inner_self_eq_norm_sq_to_K]; done)
    | (simp [inner_smul_left, inner_self_eq_norm_sq_to_K]; ring)
  rw [hcas, hre] at hB
  have hpos : 0 < ‖P‖ ^ 2 := by
    have := norm_pos_iff.mpr hP0
    positivity
  have hle := le_of_mul_le_mul_right hB hpos
  push_cast at hle
  linarith

end LayerBound

end ReciprocityTheory.ChartRestriction.DS
