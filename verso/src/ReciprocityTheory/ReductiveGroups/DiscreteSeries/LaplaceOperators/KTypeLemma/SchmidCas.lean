import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section No

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

/- English proof (translation)
Introduce `a b hab hε w hw hμ`. Assume the negation of the conclusion as `hw0`. Establish `: FiniteDimensional ℂ V` using `hV.1`. Establish `hKU : IsKUnitary ε E` using `isKUnitary_of_isInfUnitary hU`. Establish `hP : V.starProjection w = 0`.

Assume the negation of the conclusion as `hne`. Establish `hkhw` using `isKHWVec_starProjection hKU hV.2.1 hμ`. Establish `heq` using `khw_weight_eq_of_irr hE hV (Submodule.starProjection_apply_mem V w) hne hkhw`. Establish `h2` using `congr_fun heq a`. Simplify using `only [Pi.sub_apply, root, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne] at h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hperp : ∀ u ∈ layer ε E V 0, inner ℂ u w = 0`. Introduce `u hu`. Establish `hwo : w ∈ Vᗮ`. Use `Submodule.sub_starProjection_mem_orthogonal (K := V) w` as an intermediate fact.

Rewrite `this` using `[hP, sub_zero]`. Then use the resulting hypothesis. Conclude with `(Submodule.mem_orthogonal V w).1 hwo u hu`. Take `⟨P, hPnc, hP0, hPμ, hPperp⟩` from `lift_layer hE hU hV.1 hV.2.1 (k := 0) hw hperp hμ hw0`. Take `⟨xm, hxm, xp, hxp, hsum⟩` from `ncV_one_decomp hE hU hV hmono hh hbig hPnc`. Establish `hxm0 : inner ℂ xm P = 0` using `hPperp xm (Wm_le_ncV hxm) (by rw [hS xm hxm]; exact zero_mem _)`.

Establish `hmp : inner ℂ xm xp = 0` using `Wm_perp_Wp hU hxm hxp`. Establish `hxm_eq : xm = 0`. Establish `h3 : inner ℂ xm xm = 0`. Rewrite `hxm0` using `[hsum, inner_add_right, hmp, add_zero]`. Conclude with `hxm0`.

Conclude with `inner_self_eq_zero.1 h3`. Rewrite `hsum` using `[hxm_eq, zero_add]`. Establish `hPWp : P ∈ Wp ε E V` using `hsum ▸ hxp`. Take `⟨r, s, -, -, hC⟩` from `crossOp_khw hE hU hV hPnc hP0 hPμ`. Establish `hroot : lowK ε lam - root a b = lowK ε lam + root b a`.

Use extensionality with `x`. Simplify using `only [Pi.sub_apply, Pi.add_apply, root]`. Expand and normalize the polynomial expressions, which then agree. Establish `hneg` using `crossVal_neg hmono hh hab hε`. Rewrite `hneg` using `[← hroot]`.

Establish `hWp` using `Wp_bound hE hU hV hmono hh hbig hPWp`. Use `set val : ℝ := casValK ε (lowK ε lam - root a b) - n - casValK ε (lowK ε lam) with hval`. Establish `key : 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 P) P) = val * ‖P‖ ^ 2`. Establish `e` using `congrArg (fun x => RCLike.re (inner ℂ x P)) hC`. Establish `hre : ((‖P‖ : ℂ) ^ 2).re = ‖P‖ ^ 2` using `by rw [← Complex.ofReal_pow, Complex.ofReal_re]`.

Simplify using `only [inner_smul_left, inner_self_eq_norm_sq_to_K] at e`. Simplify using `at e`. Rewrite `e` using `[hre]`. Conclude with `e`. Establish `hpos : 0 < ‖P‖ ^ 2` using `by positivity`.

Establish `h4 : 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ (-2 * h - 2) * ‖P‖ ^ 2`. Rewrite `hWp` using `[key]`. Conclude with `hWp.trans (mul_le_mul_of_nonneg_right hneg hpos.le)`. Establish `h5` using `le_of_mul_le_mul_right h4 hpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sc_no_of_schmid (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) (hn : (n : ℝ) < h)
    (hS : ∀ x ∈ Wm ε E V, phi E 1 x = 0) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hε w hw hμ
  by_contra hw0
  have : FiniteDimensional ℂ V := hV.1
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  have hP : V.starProjection w = 0 := by
    by_contra hne
    have hkhw := isKHWVec_starProjection hKU hV.2.1 hμ
    have heq := khw_weight_eq_of_irr hE hV (Submodule.starProjection_apply_mem V w) hne hkhw
    have h2 := congr_fun heq a
    simp only [Pi.sub_apply, root, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne] at h2
    linarith
  have hperp : ∀ u ∈ layer ε E V 0, inner ℂ u w = 0 := by
    intro u hu
    have hwo : w ∈ Vᗮ := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := V) w
      rwa [hP, sub_zero] at this
    exact (Submodule.mem_orthogonal V w).1 hwo u hu
  obtain ⟨P, hPnc, hP0, hPμ, hPperp⟩ := lift_layer hE hU hV.1 hV.2.1 (k := 0) hw hperp hμ hw0
  obtain ⟨xm, hxm, xp, hxp, hsum⟩ := ncV_one_decomp hE hU hV hmono hh hbig hPnc
  have hxm0 : inner ℂ xm P = 0 :=
    hPperp xm (Wm_le_ncV hxm) (by rw [hS xm hxm]; exact zero_mem _)
  have hmp : inner ℂ xm xp = 0 := Wm_perp_Wp hU hxm hxp
  have hxm_eq : xm = 0 := by
    have h3 : inner ℂ xm xm = 0 := by
      rw [hsum, inner_add_right, hmp, add_zero] at hxm0
      exact hxm0
    exact inner_self_eq_zero.1 h3
  rw [hxm_eq, zero_add] at hsum
  have hPWp : P ∈ Wp ε E V := hsum ▸ hxp
  obtain ⟨r, s, -, -, hC⟩ := crossOp_khw hE hU hV hPnc hP0 hPμ
  have hroot : lowK ε lam - root a b = lowK ε lam + root b a := by
    ext x; simp only [Pi.sub_apply, Pi.add_apply, root]; ring
  have hneg := crossVal_neg hmono hh hab hε
  rw [← hroot] at hneg
  have hWp := Wp_bound hE hU hV hmono hh hbig hPWp
  set val : ℝ := casValK ε (lowK ε lam - root a b) - n - casValK ε (lowK ε lam) with hval
  have key : 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 P) P) = val * ‖P‖ ^ 2 := by
    have e := congrArg (fun x => RCLike.re (inner ℂ x P)) hC
    have hre : ((‖P‖ : ℂ) ^ 2).re = ‖P‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [inner_smul_left, inner_self_eq_norm_sq_to_K] at e
    simp at e
    rw [hre] at e
    exact e
  have hpos : 0 < ‖P‖ ^ 2 := by positivity
  have h4 : 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ (-2 * h - 2) * ‖P‖ ^ 2 := by
    rw [key] at hWp
    exact hWp.trans (mul_le_mul_of_nonneg_right hneg hpos.le)
  have h5 := le_of_mul_le_mul_right h4 hpos
  linarith

end No

/- English proof (translation)
Introduce `ε ν h c N _ _ EN W hE hU hW hS hc hint hmono hgap hneed hp hq`. Use `set lam : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam`. Establish `hlow : lowK ε lam = ν`. Use extensionality with `a`. Simplify using `only [lowK, hlam, Pi.add_apply, Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hW' : IsKIrrHW ε EN (lowK ε lam) W` using `by rw [hlow]; exact hW`. Establish `hN1 : 2 + (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε`. Unfold `hNeed`. Conclude with `le_trans (by linarith [le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))]) (le_max_left _ _)`.

Establish `hN2 : 2 + 3 * (n : ℝ) / 2 ≤ hNeed ε`. Unfold `hNeed`. Conclude with `le_trans (by linarith [le_max_left (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))]) (le_max_left _ _)`. Establish `hN3 : 16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2 ≤ hNeed ε` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Establish `hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h` using `by linarith`. Establish `hn : (n : ℝ) < h` using `by linarith`. Establish `hstd : StdGap ε lam` using `⟨hmono, h, hgap, hbig⟩`. Establish `hHC : S7.IsHCParam lam` using `⟨hmono, hint⟩`. Take `⟨T⟩` from `HW.kType_exists ε lam hHC`.

Take `⟨μ, hμ⟩` from `S7.exists_mu hHC`. Establish `hq0 : 1 ≤ S7.q0 ε` using `le_min hp hq`. Establish `h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h`. Establish `e : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ)`. Simplify using `only [S7.q0, Nat.cast_min]`.

Establish `hm : 0 ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)` using `by positivity`. Establish `hs` using `Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hPsi` using `(S7.isPsiFor_psiM ε lam h T μ hHC hμ hgap hq0 h8).1`.

Establish `hv₀ : T.w ≠ 0`. Introduce `h0`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h0, norm_zero]`. Conclude with `zero_ne_one h1`.

Establish `hσ` using `rreg_isURepOn ε`. Establish `hD` using `isDerivedOn_smE hσ`. Establish `hcas` using `casimir_eq_casVal_of_model hstd hE hU hW' (sc_no_of_schmid hE hU hW' hmono hgap hbig hn hS) hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) (datumV_isKIrrHW hPsi hv₀) (datumV_casimir hPsi T.w)`. Take `⟨w, hwW, hw0, -⟩` from `hW.2.2.2`. Establish `h1` using `hc w hwW`.

Rewrite `h1` using `[hcas w hwW]`. Conclude with `(smul_left_injective ℂ hw0 h1).symm`.
-/
theorem schmid_casimir (n : ℕ) : SchmidCasimirStatement n := by
  intro ε ν h c N _ _ EN W hE hU hW hS hc hint hmono hgap hneed hp hq
  set lam : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam
  have hlow : lowK ε lam = ν := by
    ext a; simp only [lowK, hlam, Pi.add_apply, Pi.sub_apply]; ring
  have hW' : IsKIrrHW ε EN (lowK ε lam) W := by rw [hlow]; exact hW
  have hN1 : 2 + (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN2 : 2 + 3 * (n : ℝ) / 2 ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_left (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN3 : 16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2
      ≤ hNeed ε := (le_max_left _ _).trans (le_max_right _ _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by linarith
  have hn : (n : ℝ) < h := by linarith
  have hstd : StdGap ε lam := ⟨hmono, h, hgap, hbig⟩
  have hHC : S7.IsHCParam lam := ⟨hmono, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hHC
  obtain ⟨μ, hμ⟩ := S7.exists_mu hHC
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
    have e : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by
      simp only [S7.q0, Nat.cast_min]
    have hm : 0 ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
    have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
    rw [e]
    nlinarith
  have hPsi := (S7.isPsiFor_psiM ε lam h T μ hHC hμ hgap hq0 h8).1
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hcas := casimir_eq_casVal_of_model hstd hE hU hW'
    (sc_no_of_schmid hE hU hW' hmono hgap hbig hn hS) hD.glRep (isInfUnitary_of_isDerivedOn hσ hD)
    (datumV_isKIrrHW hPsi hv₀) (datumV_casimir hPsi T.w)
  obtain ⟨w, hwW, hw0, -⟩ := hW.2.2.2
  have h1 := hc w hwW
  rw [hcas w hwW] at h1
  exact (smul_left_injective ℂ hw0 h1).symm

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
