import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

/- English proof (translation)
Establish `ho : IsOpen ((L.lattice : Set ℂ)ᶜ)` using `L.isClosed_lattice.isOpen_compl`. Establish `hc : ContinuousAt (fun z : ℂ => z + t) 0` using `by fun_prop`. Establish `: (L.lattice : Set ℂ)ᶜ ∈ nhds ((fun z : ℂ => z + t) 0)`. Apply `ho.mem_nhds` to reduce the goal to its premises. Simplify using `using ht`.

Conclude with `hc.eventually this`.
-/
theorem trans_ev (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    ∀ᶠ z in nhds (0 : ℂ), z + t ∉ L.lattice := by
  have ho : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hc : ContinuousAt (fun z : ℂ => z + t) 0 := by fun_prop
  have : (L.lattice : Set ℂ)ᶜ ∈ nhds ((fun z : ℂ => z + t) 0) := by
    apply ho.mem_nhds
    simpa using ht
  exact hc.eventually this

/- English proof (translation)
Establish `h1 : AnalyticAt ℂ L.weierstrassP ((fun z : ℂ => z + t) 0)` using `L.analyticOnNhd_weierstrassP _ (by simpa using ht)`. Establish `h2 : AnalyticAt ℂ L.derivWeierstrassP ((fun z : ℂ => z + t) 0)` using `L.analyticOnNhd_derivWeierstrassP _ (by simpa using ht)`. Establish `h3 : AnalyticAt ℂ (fun z : ℂ => z + t) 0` using `by fun_prop`. Conclude with `⟨AnalyticAt.comp (g := L.weierstrassP) (f := fun z : ℂ => z + t) h1 h3, AnalyticAt.comp (g := L.derivWeierstrassP) (f := fun z : ℂ => z + t) h2 h3⟩`.
-/
theorem trans_an (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    AnalyticAt ℂ (fun z => L.weierstrassP (z + t)) 0 ∧
      AnalyticAt ℂ (fun z => L.derivWeierstrassP (z + t)) 0 := by
  have h1 : AnalyticAt ℂ L.weierstrassP ((fun z : ℂ => z + t) 0) :=
    L.analyticOnNhd_weierstrassP _ (by simpa using ht)
  have h2 : AnalyticAt ℂ L.derivWeierstrassP ((fun z : ℂ => z + t) 0) :=
    L.analyticOnNhd_derivWeierstrassP _ (by simpa using ht)
  have h3 : AnalyticAt ℂ (fun z : ℂ => z + t) 0 := by fun_prop
  exact ⟨AnalyticAt.comp (g := L.weierstrassP) (f := fun z : ℂ => z + t) h1 h3,
    AnalyticAt.comp (g := L.derivWeierstrassP) (f := fun z : ℂ => z + t) h2 h3⟩

/- English proof (translation)
Take `⟨hR, hC, -, -⟩` from `F.taylorRing`. Establish `hff : AnalyticAt ℂ (fun z => f z * f z) 0` using `hf.mul hf`. Establish `haff : AnalyticAt ℂ (fun z => a * (f z * f z)) 0` using `analyticAt_const.mul hff`. Establish `h1` using `(hR f f hf hf).2`. Establish `h2` using `(hR (fun _ => a) (fun z => f z * f z) analyticAt_const hff).2`.

Establish `h3` using `(hR (fun z => a * (f z * f z)) (fun _ => b) haff analyticAt_const).1`. Rewrite using `[h3, h2, h1, hC, hC]`.
-/
theorem trans_taylor_quad (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b : ℂ) :
    F.taylor0 (fun z => a * (f z * f z) + b) = C a * (F.taylor0 f * F.taylor0 f) + C b := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff : AnalyticAt ℂ (fun z => f z * f z) 0 := hf.mul hf
  have haff : AnalyticAt ℂ (fun z => a * (f z * f z)) 0 := analyticAt_const.mul hff
  have h1 := (hR f f hf hf).2
  have h2 := (hR (fun _ => a) (fun z => f z * f z) analyticAt_const hff).2
  have h3 := (hR (fun z => a * (f z * f z)) (fun _ => b) haff analyticAt_const).1
  rw [h3, h2, h1, hC, hC]

/- English proof (translation)
Take `⟨hR, hC, -, -⟩` from `F.taylorRing`. Establish `hff : AnalyticAt ℂ (fun z => f z * f z) 0` using `hf.mul hf`. Establish `hfff : AnalyticAt ℂ (fun z => f z * (f z * f z)) 0` using `hf.mul hff`. Establish `hafff : AnalyticAt ℂ (fun z => a * (f z * (f z * f z))) 0` using `analyticAt_const.mul hfff`. Establish `hbf : AnalyticAt ℂ (fun z => b * f z) 0` using `analyticAt_const.mul hf`.

Establish `hbfc : AnalyticAt ℂ (fun z => b * f z + c) 0` using `hbf.add analyticAt_const`. Establish `h1` using `(hR f f hf hf).2`. Establish `h2` using `(hR f (fun z => f z * f z) hf hff).2`. Establish `h3` using `(hR (fun _ => a) (fun z => f z * (f z * f z)) analyticAt_const hfff).2`. Establish `h4` using `(hR (fun _ => b) f analyticAt_const hf).2`.

Establish `h5` using `(hR (fun z => b * f z) (fun _ => c) hbf analyticAt_const).1`. Establish `h6` using `(hR (fun z => a * (f z * (f z * f z))) (fun z => b * f z + c) hafff hbfc).1`. Rewrite using `[h6, h5, h4, h3, h2, h1, hC, hC, hC]`.
-/
theorem trans_taylor_cubic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b c : ℂ) :
    F.taylor0 (fun z => a * (f z * (f z * f z)) + (b * f z + c))
      = C a * (F.taylor0 f * (F.taylor0 f * F.taylor0 f)) + (C b * F.taylor0 f + C c) := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff : AnalyticAt ℂ (fun z => f z * f z) 0 := hf.mul hf
  have hfff : AnalyticAt ℂ (fun z => f z * (f z * f z)) 0 := hf.mul hff
  have hafff : AnalyticAt ℂ (fun z => a * (f z * (f z * f z))) 0 := analyticAt_const.mul hfff
  have hbf : AnalyticAt ℂ (fun z => b * f z) 0 := analyticAt_const.mul hf
  have hbfc : AnalyticAt ℂ (fun z => b * f z + c) 0 := hbf.add analyticAt_const
  have h1 := (hR f f hf hf).2
  have h2 := (hR f (fun z => f z * f z) hf hff).2
  have h3 := (hR (fun _ => a) (fun z => f z * (f z * f z)) analyticAt_const hfff).2
  have h4 := (hR (fun _ => b) f analyticAt_const hf).2
  have h5 := (hR (fun z => b * f z) (fun _ => c) hbf analyticAt_const).1
  have h6 := (hR (fun z => a * (f z * (f z * f z))) (fun z => b * f z + c) hafff hbfc).1
  rw [h6, h5, h4, h3, h2, h1, hC, hC, hC]

/- English proof (translation)
Take `⟨haf, hag⟩` from `trans_an L t ht`. Take `⟨hR, hC, -, hG⟩` from `F.taylorRing`. Take `⟨hD, -, -⟩` from `F.taylorDeriv`. Establish `hev` using `trans_ev L t ht`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hD _ haf]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Rewrite using `[deriv_comp_add_const, L.deriv_weierstrassP]`. Rewrite using `[← hD _ hag, ← trans_taylor_quad _ haf]`.

Apply `hG` to reduce the goal to its premises. Use `filter_upwards [hev] with z hz`. Rewrite using `[deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← (hR _ _ hag hag).2, ← trans_taylor_cubic _ haf]`.

Apply `hG` to reduce the goal to its premises. Use `filter_upwards [hev] with z hz`. Use `L.derivWeierstrassP_sq (z + t) hz` as an intermediate fact. Take the linear combination `this`.
-/
theorem trans_taylor (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    derivative ℂ (F.taylor0 (fun z => L.weierstrassP (z + t)))
        = F.taylor0 (fun z => L.derivWeierstrassP (z + t)) ∧
    derivative ℂ (F.taylor0 (fun z => L.derivWeierstrassP (z + t)))
        = C 6 * (F.taylor0 (fun z => L.weierstrassP (z + t))
            * F.taylor0 (fun z => L.weierstrassP (z + t))) + C (-(L.g₂ / 2)) ∧
    F.taylor0 (fun z => L.derivWeierstrassP (z + t)) * F.taylor0 (fun z => L.derivWeierstrassP (z + t))
        = C 4 * (F.taylor0 (fun z => L.weierstrassP (z + t))
            * (F.taylor0 (fun z => L.weierstrassP (z + t))
              * F.taylor0 (fun z => L.weierstrassP (z + t))))
          + (C (-L.g₂) * F.taylor0 (fun z => L.weierstrassP (z + t)) + C (-L.g₃)) := by
  obtain ⟨haf, hag⟩ := trans_an L t ht
  obtain ⟨hR, hC, -, hG⟩ := F.taylorRing
  obtain ⟨hD, -, -⟩ := F.taylorDeriv
  have hev := trans_ev L t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← hD _ haf]
    congr 1
    funext z
    rw [deriv_comp_add_const, L.deriv_weierstrassP]
  · rw [← hD _ hag, ← trans_taylor_quad _ haf]
    apply hG
    filter_upwards [hev] with z hz
    rw [deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]
    ring
  · rw [← (hR _ _ hag hag).2, ← trans_taylor_cubic _ haf]
    apply hG
    filter_upwards [hev] with z hz
    have := L.derivWeierstrassP_sq (z + t) hz
    linear_combination this

/- English proof (translation)
Use extensionality with `n`. Simplify using `[coeff_derivative]`.
-/
theorem trans_derivative_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    derivative S (PowerSeries.map φ f) = PowerSeries.map φ (derivative R f) := by
  ext n
  simp [coeff_derivative]

/- English proof (translation)
Establish `hs : HasSubst a` using `HasSubst.of_constantCoeff_zero' ha`. Establish `h0 : constantCoeff (f - C (constantCoeff f)) = 0` using `by simp`. Establish `h1` using `constantCoeff_subst_eq_zero (S := K) ha (f - C (constantCoeff f)) h0`. Rewrite `h1` using `[subst_sub hs, subst_C]`. Establish `h2 : constantCoeff (subst a f - C (constantCoeff f)) = 0` using `h1`.

Rewrite `h2` using `[map_sub, constantCoeff_C, sub_eq_zero]`. Conclude with `h2`.
-/
theorem trans_constSubst {K : Type*} [CommRing K] (f a : K⟦X⟧) (ha : constantCoeff a = 0) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have h1 := constantCoeff_subst_eq_zero (S := K) ha (f - C (constantCoeff f)) h0
  rw [subst_sub hs, subst_C] at h1
  have h2 : constantCoeff (subst a f - C (constantCoeff f)) = 0 := h1
  rw [map_sub, constantCoeff_C, sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Take `⟨-, -, -, hx, hy⟩` from `A.wSerFactor K (A.shortW g2 g3)`. Establish `ht : constantCoeff (A.tDen (A.shortW g2 g3) xP) = 1` using `by simp [A.tDen, hx]`. Establish `h1 : (A.shortW g2 g3).a₁ = 0` using `rfl`. Establish `h3 : (A.shortW g2 g3).a₃ = 0` using `rfl`. Prove the components needed by the constructor for the conclusion.

Simplify using `[A.yPlus, A.xPlus, A.nS, hx, hy, ht, h1, h3]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[A.xPlus]`.
-/
theorem trans_plus_const {K : Type} [Field K] (g2 g3 xP yP : K) :
    constantCoeff (A.yPlus (A.shortW g2 g3) xP yP) = yP ∧
    constantCoeff (A.xPlus (A.shortW g2 g3) xP yP) = xP := by
  obtain ⟨-, -, -, hx, hy⟩ := A.wSerFactor K (A.shortW g2 g3)
  have ht : constantCoeff (A.tDen (A.shortW g2 g3) xP) = 1 := by simp [A.tDen, hx]
  have h1 : (A.shortW g2 g3).a₁ = 0 := rfl
  have h3 : (A.shortW g2 g3).a₃ = 0 := rfl
  constructor
  · simp [A.yPlus, A.xPlus, A.nS, hx, hy, ht, h1, h3]
    ring
  · simp [A.xPlus]

/- English proof (translation)
Take `⟨e1, e2, e3⟩` from `trans_taylor L t ht`. Use `set p := F.taylor0 (fun z => L.weierstrassP (z + t)) with hp`. Use `set q := F.taylor0 (fun z => L.derivWeierstrassP (z + t)) with hq`. Use `set W := A.shortW (ι L.g₂) (ι L.g₃) with hW`. Establish `a1 : W.a₁ = 0` using `rfl`.

Establish `a2 : W.a₂ = 0` using `rfl`. Establish `a3 : W.a₃ = 0` using `rfl`. Establish `a4 : W.a₄ = -ι L.g₂ / 4` using `rfl`. Establish `a6 : W.a₆ = -ι L.g₃ / 4` using `rfl`. Establish `hpt : W.toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2)`.

Rewrite using `[WeierstrassCurve.Affine.equation_iff, a1, a2, a3, a4, a6]`. Use `congrArg ι (L.derivWeierstrassP_sq t ht)` as an intermediate fact. Simplify using `only [map_pow, map_sub, map_mul, map_ofNat] at this`. Take the linear combination `(1 / 4 : ℂ_[l]) * this`. Take `⟨hfl, -, -⟩` from `A.plusZ ℂ_[l] W _ _ hpt`.

Use `set P := PowerSeries.map (ι : ℂ →+* ℂ_[l]) p with hP`. Use `set Q := PowerSeries.map (ι : ℂ →+* ℂ_[l]) q with hQ`. Establish `i2 : ι 2 = 2` using `map_ofNat ι 2`. Establish `i4 : ι 4 = 4` using `map_ofNat ι 4`. Establish `i6 : ι 6 = 6` using `map_ofNat ι 6`.

Establish `E1 : derivative ℂ_[l] P = Q` using `by rw [hP, trans_derivative_map, e1]`. Establish `E2 : derivative ℂ_[l] Q = C 6 * (P * P) + C (-(ι L.g₂ / 2))`. Rewrite using `[hQ, trans_derivative_map, e2]`. Simplify using `[hP, i2, i6]`. Establish `E3 : Q * Q = C 4 * (P * (P * P)) + (C (-ι L.g₂) * P + C (-ι L.g₃))`.

Rewrite using `[hQ, ← map_mul, e3]`. Simplify using `[hP, i4]`. Establish `h2 : (C (1 / 2 : ℂ_[l]) : ℂ_[l]⟦X⟧) * 2 = 1`. Rewrite using `[← map_ofNat (C : ℂ_[l] →+* ℂ_[l]⟦X⟧) 2, ← map_mul]`. Evaluate the numerical expressions.

Establish `hfl' : A.IsFlow (A.curveS W) (derivative ℂ_[l]) P (C (1 / 2 : ℂ_[l]) * Q)`. Establish `c4 : (C (-ι L.g₂ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₂)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `c6 : (C (-ι L.g₃ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₃)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `c2 : (C (-(ι L.g₂ / 2)) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (-ι L.g₂)`.

Rewrite using `[← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `k4 : (C 4 : ℂ_[l]⟦X⟧) = 4` using `map_ofNat _ 4`. Establish `k6 : (C 6 : ℂ_[l]⟦X⟧) = 6` using `map_ofNat _ 6`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, a1, a2, a3, a4, a6, map_zero, c4, c6]`. Rewrite `E3` using `[k4]`. Take the linear combination `(C (1 / 2 : ℂ_[l]) * C (1 / 2)) * E3 + (P ^ 3 * (C (1 / 2 : ℂ_[l]) * 2 + 1)) * h2`.

Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, a1, a3, map_zero]`. Rewrite using `[E1]`. Take the linear combination `(-Q) * h2`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, a1, a2, a4, map_zero, c4]`. Rewrite using `[← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul, E2, k6, c2]`.

Take the linear combination `(3 * P ^ 2) * h2`. Establish `hc0 : constantCoeff (A.expSer W) = 0` using `(A.expSpec ℂ_[l] W).1`. Use `(A.flowUniqueZ ℂ_[l] W _ _ _ _ hfl' hfl ?_ ?_).1` and prove the remaining obligations. Rewrite using `[trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).2, hP, hp]`. Simplify using `[← coeff_zero_eq_constantCoeff_apply, F.taylor0]`.

Rewrite using `[trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).1, hQ, hq]`. Simplify using `[← coeff_zero_eq_constantCoeff_apply, F.taylor0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trans_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ)
    (ht : t ∉ L.lattice) :
    PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 (fun z => L.weierstrassP (z + t)))
      = (A.xPlus (A.shortW (ι L.g₂) (ι L.g₃)) (ι (L.weierstrassP t))
          (ι (L.derivWeierstrassP t) / 2)).subst (A.expSer (A.shortW (ι L.g₂) (ι L.g₃))) := by
  obtain ⟨e1, e2, e3⟩ := trans_taylor L t ht
  set p := F.taylor0 (fun z => L.weierstrassP (z + t)) with hp
  set q := F.taylor0 (fun z => L.derivWeierstrassP (z + t)) with hq
  set W := A.shortW (ι L.g₂) (ι L.g₃) with hW
  have a1 : W.a₁ = 0 := rfl
  have a2 : W.a₂ = 0 := rfl
  have a3 : W.a₃ = 0 := rfl
  have a4 : W.a₄ = -ι L.g₂ / 4 := rfl
  have a6 : W.a₆ = -ι L.g₃ / 4 := rfl
  have hpt : W.toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    rw [WeierstrassCurve.Affine.equation_iff, a1, a2, a3, a4, a6]
    have := congrArg ι (L.derivWeierstrassP_sq t ht)
    simp only [map_pow, map_sub, map_mul, map_ofNat] at this
    linear_combination (1 / 4 : ℂ_[l]) * this
  obtain ⟨hfl, -, -⟩ := A.plusZ ℂ_[l] W _ _ hpt
  set P := PowerSeries.map (ι : ℂ →+* ℂ_[l]) p with hP
  set Q := PowerSeries.map (ι : ℂ →+* ℂ_[l]) q with hQ
  have i2 : ι 2 = 2 := map_ofNat ι 2
  have i4 : ι 4 = 4 := map_ofNat ι 4
  have i6 : ι 6 = 6 := map_ofNat ι 6
  have E1 : derivative ℂ_[l] P = Q := by rw [hP, trans_derivative_map, e1]
  have E2 : derivative ℂ_[l] Q = C 6 * (P * P) + C (-(ι L.g₂ / 2)) := by
    rw [hQ, trans_derivative_map, e2]
    simp [hP, i2, i6]
  have E3 : Q * Q = C 4 * (P * (P * P)) + (C (-ι L.g₂) * P + C (-ι L.g₃)) := by
    rw [hQ, ← map_mul, e3]
    simp [hP, i4]
  have h2 : (C (1 / 2 : ℂ_[l]) : ℂ_[l]⟦X⟧) * 2 = 1 := by
    rw [← map_ofNat (C : ℂ_[l] →+* ℂ_[l]⟦X⟧) 2, ← map_mul]
    norm_num
  have hfl' : A.IsFlow (A.curveS W) (derivative ℂ_[l]) P (C (1 / 2 : ℂ_[l]) * Q) := by
    have c4 : (C (-ι L.g₂ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul, ← map_mul]; congr 1; ring
    have c6 : (C (-ι L.g₃ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₃) := by
      rw [← map_mul, ← map_mul]; congr 1; ring
    have c2 : (C (-(ι L.g₂ / 2)) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul]; congr 1; ring
    have k4 : (C 4 : ℂ_[l]⟦X⟧) = 4 := map_ofNat _ 4
    have k6 : (C 6 : ℂ_[l]⟦X⟧) = 6 := map_ofNat _ 6
    refine ⟨?_, ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, a1, a2, a3, a4, a6, map_zero, c4, c6]
      rw [k4] at E3
      linear_combination (C (1 / 2 : ℂ_[l]) * C (1 / 2)) * E3 +
        (P ^ 3 * (C (1 / 2 : ℂ_[l]) * 2 + 1)) * h2
    · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, a1, a3, map_zero]
      rw [E1]
      linear_combination (-Q) * h2
    · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
        a1, a2, a4, map_zero, c4]
      rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul, E2, k6, c2]
      linear_combination (3 * P ^ 2) * h2
  have hc0 : constantCoeff (A.expSer W) = 0 := (A.expSpec ℂ_[l] W).1
  refine (A.flowUniqueZ ℂ_[l] W _ _ _ _ hfl' hfl ?_ ?_).1
  · rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).2, hP, hp]
    simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
  · rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).1, hQ, hq]
    simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
    ring

end ReciprocityTheory.ChartRestriction.L1
