import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace TaylorSigmaUniqueness

open PowerSeries in

/- English proof (translation)
Establish `hV' : derivative ℂ V = -P`. Apply `mul_left_cancel₀ (X_ne_zero (R := ℂ))` to reduce the goal to its premises. Rewrite using `[hV, mul_neg]`. Establish `hU' : derivative ℂ U = V * U` using `mul_left_cancel₀ (X_ne_zero (R := ℂ)) hU`. Establish `hVp : V = -B.prim P`.

Use `derivative.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hV', map_neg]`. Conclude with `congrArg Neg.neg (B.dz_prim P).symm`. Rewrite using `[hV0, map_neg, B.constantCoeff_prim, neg_zero]`. Establish `hS0 : constantCoeff (B.sigS P) = 0`.

Rewrite using `[B.sigS, map_neg, B.constantCoeff_prim, neg_zero]`. Establish `hS0' : constantCoeff (-B.sigS P) = 0` using `by rw [map_neg, hS0, neg_zero]`. Establish `hSd : derivative ℂ (B.sigS P) = V`. Rewrite using `[B.sigS, map_neg, hVp]`. Conclude with `congrArg Neg.neg (B.dz_prim _)`.

Establish `key : U * (C.mvExp (-B.sigS P) : PowerSeries ℂ) = 1`. Use `derivative.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, C.derivative_mvExp hS0', map_neg, hSd, hU', Derivation.map_one_eq_zero]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_mul, hU0, map_one, one_mul]`. Conclude with `C.constantCoeff_mvExp hS0'`. Establish `h2 : (C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P) = 1` using `C.mvExp_neg hS0`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma formal_unique (P U V : PowerSeries ℂ) (hV : X * derivative ℂ V = -(X * P))
    (hV0 : constantCoeff V = 0) (hU : X * derivative ℂ U = X * (V * U))
    (hU0 : constantCoeff U = 1) : U = B.fExp (B.sigS P) := by
  have hV' : derivative ℂ V = -P := by
    apply mul_left_cancel₀ (X_ne_zero (R := ℂ))
    rw [hV, mul_neg]
  have hU' : derivative ℂ U = V * U := mul_left_cancel₀ (X_ne_zero (R := ℂ)) hU
  have hVp : V = -B.prim P := by
    refine derivative.ext ?_ ?_
    · rw [hV', map_neg]
      exact congrArg Neg.neg (B.dz_prim P).symm
    · rw [hV0, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0' : constantCoeff (-B.sigS P) = 0 := by rw [map_neg, hS0, neg_zero]
  have hSd : derivative ℂ (B.sigS P) = V := by
    rw [B.sigS, map_neg, hVp]
    exact congrArg Neg.neg (B.dz_prim _)
  have key : U * (C.mvExp (-B.sigS P) : PowerSeries ℂ) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, C.derivative_mvExp hS0', map_neg, hSd, hU', Derivation.map_one_eq_zero]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, hU0, map_one, one_mul]
      exact C.constantCoeff_mvExp hS0'
  have h2 : (C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P) = 1 := C.mvExp_neg hS0
  calc U = U * ((C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P)) := by rw [h2, mul_one]
    _ = C.mvExp (B.sigS P) := by rw [← mul_assoc, key, one_mul]
    _ = B.fExp (B.sigS P) := rfl

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor0, PowerSeries.coeff_mk]`. Simplify using the standard rewrite rules.
-/
lemma constantCoeff_taylor0 (f : ℂ → ℂ) : PowerSeries.constantCoeff (taylor0 f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor0, PowerSeries.coeff_mk]
  simp

def u (L : PeriodPair) (z : ℂ) : ℂ := ∏' l : L.lattice, wFactor (l : ℂ) z

/- English proof (translation)
The claim follows from `SigmaBasic.differentiable_tprod sigma_product_locally_uniform L`.
-/
lemma differentiable_u (L : PeriodPair) : Differentiable ℂ (u L) :=
  SigmaBasic.differentiable_tprod sigma_product_locally_uniform L

/- English proof (translation)
Simplify using `[u, SigmaBasic.wFactor_zero_right]`.
-/
lemma u_zero (L : PeriodPair) : u L 0 = 1 := by
  simp [u, SigmaBasic.wFactor_zero_right]

/- English proof (translation)
The claim follows from `(AnalyticIdentityTheoremsZetaFacts.differentiableOn_zetaExcept L 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)`.
-/
lemma analyticAt_v (L : PeriodPair) : AnalyticAt ℂ (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) 0 :=
  (AnalyticIdentityTheoremsZetaFacts.differentiableOn_zetaExcept L 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)

/- English proof (translation)
The claim follows from `(L.differentiableOn_weierstrassPExcept 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)`.
-/
lemma analyticAt_pExcept (L : PeriodPair) : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 :=
  (L.differentiableOn_weierstrassPExcept 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)

/- English proof (translation)
Use `filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz`. Distinguish the cases in `h0 : z = 0`. Simplify using `[h0]`. Establish `hzl : z ∉ L.lattice` using `fun h => hz ⟨h, h0⟩`. Establish `h1 : HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z` using `sigmaLogDeriv_of sigma_product_locally_uniform sigma_summable zeta_summable L z hzl`.

Establish `h2 : HasDerivAt (wSigma L) (1 * u L z + z * deriv (u L) z) z` using `(hasDerivAt_id z).mul (differentiable_u L z).hasDerivAt`. Establish `h3` using `h1.unique h2`. Rewrite `h3` using `[← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L z]`. Establish `h4 : wSigma L z = z * u L z` using `rfl`. Rewrite `h3` using `[h4]`.

Establish `h5 : (1 / z) * z = 1` using `by field_simp`. Take the linear combination `-h3 + u L z * h5`.
-/
lemma ode_u (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (u L) z = z * (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z :=
    sigmaLogDeriv_of sigma_product_locally_uniform sigma_summable zeta_summable L z hzl
  have h2 : HasDerivAt (wSigma L) (1 * u L z + z * deriv (u L) z) z :=
    (hasDerivAt_id z).mul (differentiable_u L z).hasDerivAt
  have h3 := h1.unique h2
  rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L z] at h3
  have h4 : wSigma L z = z * u L z := rfl
  rw [h4] at h3
  have h5 : (1 / z) * z = 1 := by field_simp
  linear_combination -h3 + u L z * h5

/- English proof (translation)
Use `filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz`. Distinguish the cases in `h0 : z = 0`. Simplify using `[h0]`. Establish `hzl : z ∉ L.lattice` using `fun h => hz ⟨h, h0⟩`. Establish `h1 : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z` using `zeta_has_deriv L z hzl`.

Establish `h2 : HasDerivAt (fun w : ℂ => 1 / w) (-(1 / z ^ 2)) z`. Simplify `hasDerivAt_inv h0` using `only [one_div]`. Establish `h3 : AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 = fun w => wZeta L w - 1 / w`. Use function extensionality and compare the values at `w`. Rewrite using `[← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L w]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : deriv (fun w => wZeta L w - 1 / w) z = -(L.weierstrassP z) - -(1 / z ^ 2)` using `(h1.sub h2).deriv`. Rewrite using `[h3, h4]`. Establish `h5` using `L.weierstrassPExcept_add 0 z`. Simplify using `only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at h5`.

Rewrite using `[← h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ode_v (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -(z * L.weierstrassPExcept 0 z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z := zeta_has_deriv L z hzl
  have h2 : HasDerivAt (fun w : ℂ => 1 / w) (-(1 / z ^ 2)) z := by
    simpa only [one_div] using hasDerivAt_inv h0
  have h3 : AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 = fun w => wZeta L w - 1 / w := by
    funext w
    rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L w]
    ring
  have h4 : deriv (fun w => wZeta L w - 1 / w) z = -(L.weierstrassP z) - -(1 / z ^ 2) :=
    (h1.sub h2).deriv
  rw [h3, h4]
  have h5 := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  rw [← h5]
  ring

end TaylorSigmaUniqueness

open TaylorSigmaUniqueness in

/- English proof (translation)
Introduce `L`. Take `⟨hadd, hC, hX, hgerm⟩` from `hr`. Establish `hid : AnalyticAt ℂ (fun z : ℂ => z) 0` using `analyticAt_id`. Establish `hu : AnalyticAt ℂ (u L) 0` using `(differentiable_u L).analyticAt 0`. Establish `hv` using `analyticAt_v L`.

Establish `hp` using `analyticAt_pExcept L`. Establish `e1 : taylor0 (wSigma L) = PowerSeries.X * taylor0 (u L)`. Use `(hadd (fun z => z) (u L) hid hu).2` as an intermediate fact. Rewrite `this` using `[hX]`. Conclude with `this`.

Establish `eU : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (u L)) = PowerSeries.X * (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) * taylor0 (u L))`. Establish `hvu : AnalyticAt ℂ (fun z => AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) 0` using `hv.mul hu`. Rewrite using `[← hd.1 _ hu, ← hX, ← (hadd _ _ hid hu.deriv).2, ← (hadd _ _ hv hu).2, ← (hadd _ _ hid hvu).2]`. Conclude with `hgerm _ _ (ode_u L)`. Establish `eV : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0)) = -(PowerSeries.X * pSeries L)`.

Establish `hneg : taylor0 (fun z => (-1 : ℂ) * (z * L.weierstrassPExcept 0 z)) = -(PowerSeries.X * pSeries L)`. Establish `hzp : AnalyticAt ℂ (fun z => z * L.weierstrassPExcept 0 z) 0` using `hid.mul hp`. Rewrite using `[(hadd (fun _ => (-1 : ℂ)) _ analyticAt_const hzp).2, hC, (hadd _ _ hid hp).2, hX, pSeries]`. Simplify using the standard rewrite rules. Rewrite using `[← hd.1 _ hv, ← hneg, ← hX, ← (hadd _ _ hid hv.deriv).2]`.

Use `hgerm _ _ ((ode_v L).mono fun z hz => ?_)` and prove the remaining obligations. Use `show z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -1 * (z * L.weierstrassPExcept 0 z)`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, B.sigma]`.

Use `congr 1`. Use `formal_unique (pSeries L) _ _ eV ?_ eU ?_` and prove the remaining obligations. Rewrite using `[constantCoeff_taylor0, AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_zero]`. Rewrite using `[constantCoeff_taylor0, u_zero]`.
-/
theorem taylorSigma_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorSigma := by
  intro L
  obtain ⟨hadd, hC, hX, hgerm⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hu : AnalyticAt ℂ (u L) 0 := (differentiable_u L).analyticAt 0
  have hv := analyticAt_v L
  have hp := analyticAt_pExcept L
  have e1 : taylor0 (wSigma L) = PowerSeries.X * taylor0 (u L) := by
    have := (hadd (fun z => z) (u L) hid hu).2
    rw [hX] at this
    exact this
  have eU : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (u L))
      = PowerSeries.X * (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) * taylor0 (u L)) := by
    have hvu : AnalyticAt ℂ (fun z => AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) 0 := hv.mul hu
    rw [← hd.1 _ hu, ← hX, ← (hadd _ _ hid hu.deriv).2, ← (hadd _ _ hv hu).2,
      ← (hadd _ _ hid hvu).2]
    exact hgerm _ _ (ode_u L)
  have eV : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0))
      = -(PowerSeries.X * pSeries L) := by
    have hneg : taylor0 (fun z => (-1 : ℂ) * (z * L.weierstrassPExcept 0 z))
        = -(PowerSeries.X * pSeries L) := by
      have hzp : AnalyticAt ℂ (fun z => z * L.weierstrassPExcept 0 z) 0 := hid.mul hp
      rw [(hadd (fun _ => (-1 : ℂ)) _ analyticAt_const hzp).2, hC,
        (hadd _ _ hid hp).2, hX, pSeries]
      simp
    rw [← hd.1 _ hv, ← hneg, ← hX, ← (hadd _ _ hid hv.deriv).2]
    refine hgerm _ _ ((ode_v L).mono fun z hz => ?_)
    show z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -1 * (z * L.weierstrassPExcept 0 z)
    rw [hz]; ring
  rw [e1, B.sigma]
  congr 1
  refine formal_unique (pSeries L) _ _ eV ?_ eU ?_
  · rw [constantCoeff_taylor0, AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_zero]
  · rw [constantCoeff_taylor0, u_zero]

/- English proof (translation)
Introduce `L`. Take `⟨hadd, hC, hX, -⟩` from `hr`. Establish `hid : AnalyticAt ℂ (fun z : ℂ => z) 0` using `analyticAt_id`. Establish `hzz : AnalyticAt ℂ (fun z : ℂ => z * z) 0` using `hid.mul hid`. Establish `hf : AnalyticAt ℂ (fun z : ℂ => -(s2 L / 2) * (z * z)) 0` using `analyticAt_const.mul hzz`.

Establish `hef : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(s2 L / 2) * (z * z))) 0` using `hf.cexp`. Establish `hTf : taylor0 (fun z : ℂ => -(s2 L / 2) * (z * z)) = -(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2)`. Rewrite using `[(hadd (fun _ => -(s2 L / 2)) _ analyticAt_const hzz).2, hC, (hadd _ _ hid hid).2, hX, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfun : sgStar L = fun z => wSigma L z * Complex.exp (-(s2 L / 2) * (z * z))`.

Use function extensionality and compare the values at `z`. Rewrite using `[sgStar]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, (hadd _ _ ((hent L).analyticAt 0) hef).2, h L, he _ hf (by simp), hTf, B.sgStar]`.
-/
theorem taylorSgStar_of (h : TaylorSigma) (hr : TaylorRing) (he : TaylorExp) (hent : SigmaEntire) :
    TaylorSgStar := by
  intro L
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hzz : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hid.mul hid
  have hf : AnalyticAt ℂ (fun z : ℂ => -(s2 L / 2) * (z * z)) 0 := analyticAt_const.mul hzz
  have hef : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(s2 L / 2) * (z * z))) 0 := hf.cexp
  have hTf : taylor0 (fun z : ℂ => -(s2 L / 2) * (z * z))
      = -(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) := by
    rw [(hadd (fun _ => -(s2 L / 2)) _ analyticAt_const hzz).2, hC,
      (hadd _ _ hid hid).2, hX, map_neg]
    ring
  have hfun : sgStar L = fun z => wSigma L z * Complex.exp (-(s2 L / 2) * (z * z)) := by
    funext z
    rw [sgStar]
    congr 2
    ring
  rw [hfun, (hadd _ _ ((hent L).analyticAt 0) hef).2, h L, he _ hf (by simp), hTf, B.sgStar]

namespace TaylorSigmaUniqueness

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [C.dblInt, B.prim, PowerSeries.coeff_mk]`. Break down `n with _ | _ | n` into its components or cases. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish `h1 : ((n : ℂ) + 1 + 1) ≠ 0`. Establish `: ((n + 2 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Move the coercions through the operations in `at this`. Introduce `h`. Apply `this` to reduce the goal to its premises.

Take the linear combination `h`. Establish `h2 : ((n : ℂ) + 1) ≠ 0`. Establish `: ((n + 1 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Move the coercions through the operations in `at this`. Conclude with `this`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.
-/
lemma dblInt_eq (e : PowerSeries ℂ) : C.dblInt e = B.prim (B.prim e) := by
  ext n
  simp only [C.dblInt, B.prim, PowerSeries.coeff_mk]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h1 : ((n : ℂ) + 1 + 1) ≠ 0 := by
      have : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      intro h; apply this; linear_combination h
    have h2 : ((n : ℂ) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      exact this
    simp
    field_simp

end TaylorSigmaUniqueness

open TaylorSigmaUniqueness in

/- English proof (translation)
Introduce `L`. Rewrite using `[h L, B.sgStar, B.sigma, C.sgStar, C.lam, dblInt_eq, mul_assoc]`. Use `congr 1`. Establish `h1 : MvPowerSeries.constantCoeff (B.sigS (pSeries L)) = 0`. Establish `: PowerSeries.constantCoeff (B.sigS (pSeries L)) = 0`.

Rewrite using `[B.sigS, map_neg, B.constantCoeff_prim, neg_zero]`. Conclude with `this`. Establish `h2 : MvPowerSeries.constantCoeff (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0`. Establish `: PowerSeries.constantCoeff (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0` using `by simp`. Conclude with `this`.

Rewrite using `[← B.fExp_add h1 h2, B.sigS, ← neg_add]`. Both sides reduce to the same expression.
-/
theorem taylorSgStar'_of (h : TaylorSgStar) : TaylorSgStar' := by
  intro L
  rw [h L, B.sgStar, B.sigma, C.sgStar, C.lam, dblInt_eq, mul_assoc]
  congr 1
  have h1 : MvPowerSeries.constantCoeff (B.sigS (pSeries L)) = 0 := by
    have : PowerSeries.constantCoeff (B.sigS (pSeries L)) = 0 := by
      rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
    exact this
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by
    have : PowerSeries.constantCoeff
        (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by simp
    exact this
  rw [← B.fExp_add h1 h2, B.sigS, ← neg_add]
  rfl

end Formalism.L2.Th1.F
