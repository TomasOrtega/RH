import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.SchwartzFunctionalEqZeroOfDense

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Set `L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V` to `(toEuclidean (E := V)).symm`. Take `⟨w, hw, hlow⟩` from `lower_bound L Q hpos`. Establish `hq : (fun x => -(Q (L x) (L x) : ℂ) - Complex.I * (Q' (L x) (L x) : ℂ)).HasTemperateGrowth` using `(Complex.ofRealCLM.hasTemperateGrowth.comp (quad_tg L Q)).neg.sub ((Function.HasTemperateGrowth.const _).mul (Complex.ofRealCLM.hasTemperateGrowth.comp (quad_tg L Q')))`. Set `g` to `GlobalTheory.CompanionTheory.OM.GaussSch.cexpSchwartz hq hw fun x => by`. Simplify using `using hlow x`.

Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (-(Q (L (L.symm x)) (L (L.symm x)) : ℂ) - Complex.I * (Q' (L (L.symm x)) (L (L.symm x)) : ℂ)) = _`. Rewrite using `[L.apply_symm_apply, one_mul]`.
-/
theorem exists_gauss (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hpos : ∀ x, x ≠ 0 → 0 < Q x x) :
    ∃ f : SchwartzMap V ℂ, ∀ x, f x = 1 * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] V := (toEuclidean (E := V)).symm
  obtain ⟨w, hw, hlow⟩ := lower_bound L Q hpos
  have hq : (fun x => -(Q (L x) (L x) : ℂ) - Complex.I * (Q' (L x) (L x) : ℂ)).HasTemperateGrowth :=
    (Complex.ofRealCLM.hasTemperateGrowth.comp (quad_tg L Q)).neg.sub
      ((Function.HasTemperateGrowth.const _).mul (Complex.ofRealCLM.hasTemperateGrowth.comp (quad_tg L Q')))
  let g := GlobalTheory.CompanionTheory.OM.GaussSch.cexpSchwartz hq hw fun x => by
    simpa using hlow x
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g, fun x => ?_⟩
  change Complex.exp (-(Q (L (L.symm x)) (L (L.symm x)) : ℂ) - Complex.I * (Q' (L (L.symm x)) (L (L.symm x)) : ℂ)) = _
  rw [L.apply_symm_apply, one_mul]

/- English proof (translation)
Establish `e : (fun t : ℝ => Q (x + t • a) (x + t • a)) = fun t => Q x x + t * (2 * Q x a) + t * (t * Q a a)`. Use function extensionality and compare the values at `t`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hs a x]`. Expand and normalize the polynomial expressions, which then agree. Establish `h : HasDerivAt (fun t : ℝ => Q (x + t • a) (x + t • a)) (2 * Q x a) 0`.

Rewrite using `[e]`. Establish `h1` using `((hasDerivAt_id (0 : ℝ)).mul_const (2 * Q x a)).const_add (Q x x)`. Establish `h2` using `(hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const (Q a a))`. Conclude with `(h1.add h2).congr_deriv (by simp)`. Simplify using `using h.ofReal_comp`.
-/
theorem hasFDerivAt_quad (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, Q x y = Q y x) (x a : V) :
    HasDerivAt (fun t : ℝ => (Q (x + t • a) (x + t • a) : ℂ)) (2 * Q x a) 0 := by
  have e : (fun t : ℝ => Q (x + t • a) (x + t • a)) = fun t => Q x x + t * (2 * Q x a) + t * (t * Q a a) := by
    funext t
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hs a x]
    ring
  have h : HasDerivAt (fun t : ℝ => Q (x + t • a) (x + t • a)) (2 * Q x a) 0 := by
    rw [e]
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (2 * Q x a)).const_add (Q x x)
    have h2 := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const (Q a a))
    exact (h1.add h2).congr_deriv (by simp)
  simpa using h.ofReal_comp

/- English proof (translation)
Establish `h0 : HasDerivAt (fun t : ℝ => x + t • a) a 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x`. Establish `h1 : HasDerivAt (fun t : ℝ => f (x + t • a)) (fderiv ℝ f x a) 0`. Use `(f.hasFDerivAt (x + (0 : ℝ) • a)).comp_hasDerivAt (0 : ℝ) h0` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.

Establish `h2` using `((hasFDerivAt_quad Q hs x a).neg.sub ((hasFDerivAt_quad Q' hs' x a).const_mul Complex.I)).cexp`. Simplify using `only [hf, one_mul] at h1 ⊢`. Rewrite using `[h1.unique h2]`. Simplify using `only [Pi.sub_apply, Pi.neg_apply, zero_smul, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_gauss {Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hs : ∀ x y, Q x y = Q y x) (hs' : ∀ x y, Q' x y = Q' y x)
    {f : SchwartzMap V ℂ} (hf : ∀ x, f x = 1 * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ))) (x a : V) :
    fderiv ℝ f x a = -(2 * Q x a + Complex.I * (2 * Q' x a)) * f x := by
  have h0 : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have h1 : HasDerivAt (fun t : ℝ => f (x + t • a)) (fderiv ℝ f x a) 0 := by
    have := (f.hasFDerivAt (x + (0 : ℝ) • a)).comp_hasDerivAt (0 : ℝ) h0
    simpa [Function.comp_def] using this
  have h2 := ((hasFDerivAt_quad Q hs x a).neg.sub ((hasFDerivAt_quad Q' hs' x a).const_mul Complex.I)).cexp
  simp only [hf, one_mul] at h1 ⊢
  rw [h1.unique h2]
  simp only [Pi.sub_apply, Pi.neg_apply, zero_smul, add_zero]
  ring

def om (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V × V) : ℝ := T p.1 q.2 - T q.1 p.2

/- English proof (translation)
Set `K : V →ₗ[ℝ] V` to `LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V`. Establish `hK : ∀ b, b ≠ 0 → T (K b) b < 0` using `fun b hb => by`. Use `h3 (0, b) fun h => hb (congrArg Prod.snd h)` as an intermediate fact. Simplify `this` using `[om, K]`. Establish `inj : Function.Injective K` using `(injective_iff_map_eq_zero K).2 fun b h => by`.

Assume the negation of the conclusion as `hb`. Simplify `hK b hb` using `[h]`. Set `e` to `LinearEquiv.ofInjectiveEndo K inj`. Set `c : V →ₗ[ℝ] V` to `-e.symm.toLinearMap`. Establish `hc : ∀ y, (J (0, c y)).1 = -y` using `fun y => by`.

Express the relevant statement in the definitionally equal form `K (-e.symm y) = _`. Rewrite using `[map_neg]`. Conclude with `congrArg _ (e.apply_symm_apply y)`. Set `c' : V →ₗ[ℝ] V` to `LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V ∘ₗ c`. Establish `hc' : ∀ y, (J (0, c y)).2 = c' y` using `fun _ => rfl`.

Set `Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` to `Real.pi • (T ∘ₗ c)`. Set `Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` to `Real.pi • (T ∘ₗ c')`. Establish `hQ : ∀ x y, Q x y = Real.pi * T y (c x)` using `fun x y => by rw [hT]; rfl`. Establish `hQ' : ∀ x y, Q' x y = Real.pi * T y (c' x)` using `fun x y => by rw [hT]; rfl`. Establish `s1 : ∀ x y, Q x y = Q y x` using `fun x y => by`.

Use `h1 (0, c x) (0, c y)` as an intermediate fact. Simplify using `only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply] at this`. Rewrite using `[hQ, hQ]`. Use `congr 1`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `s2 : ∀ x y, Q' x y = Q' y x` using `fun x y => by`. Use `h2 (0, c x) (0, c y)` as an intermediate fact. Simplify using `only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply] at this`. Rewrite using `[hQ', hQ']`. Use `congr 1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `pos : ∀ x, x ≠ 0 → 0 < Q x x` using `fun x hx => by`. Use `h3 (0, c x) fun h => hx (by` as an intermediate fact. Use `hc x` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Conclude with `neg_eq_zero.1 this.symm)`. Simplify using `only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply] at this`. Rewrite using `[hQ]`. Conclude with `mul_pos Real.pi_pos (by linarith)`. Take `⟨f, hf⟩` from `exists_gauss Q Q' pos`.

Use `⟨Q, Q', f, pos, hf, fun p x => ?_⟩` and prove the remaining obligations. Establish `a1` using `h1 p (0, c x)`. Establish `a2` using `h2 p (0, c x)`. Simplify using `only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply, sub_zero] at a1 a2`. Rewrite using `[fderiv_gauss s1 s2 hf, fderiv_gauss s1 s2 hf, hQ, hQ, hQ', hQ', a1, show T (J p).1 (c' x) = T p.1 (c x) - T x (J p).2 by linarith]`.

Use `push_cast`. Take the linear combination `((2 * Real.pi) * f x * (T p.1 (c' x) + T x p.2 : ℂ)) * Complex.I_mul_I`.
-/
theorem exists_vacuum (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ x y, T x y = T y x) (J : V × V →ₗ[ℝ] V × V)
    (h1 : ∀ p q, om T (J p) q = -om T p (J q)) (h2 : ∀ p q, om T (J p) (J q) = om T p q)
    (h3 : ∀ p, p ≠ 0 → 0 < om T p (J p)) :
    ∃ (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (f : SchwartzMap V ℂ), (∀ x, x ≠ 0 → 0 < Q x x) ∧
      (∀ x, f x = 1 * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ))) ∧
      ∀ p x, fderiv ℝ f x (J p).1 + (-(2 * Real.pi * Complex.I) * (T x (J p).2 : ℂ)) * f x =
        Complex.I * (fderiv ℝ f x p.1 + (-(2 * Real.pi * Complex.I) * (T x p.2 : ℂ)) * f x) := by
  let K : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V
  have hK : ∀ b, b ≠ 0 → T (K b) b < 0 := fun b hb => by
    have := h3 (0, b) fun h => hb (congrArg Prod.snd h)
    simpa [om, K] using this
  have inj : Function.Injective K := (injective_iff_map_eq_zero K).2 fun b h => by
    by_contra hb
    simpa [h] using hK b hb
  let e := LinearEquiv.ofInjectiveEndo K inj
  let c : V →ₗ[ℝ] V := -e.symm.toLinearMap
  have hc : ∀ y, (J (0, c y)).1 = -y := fun y => by
    change K (-e.symm y) = _
    rw [map_neg]
    exact congrArg _ (e.apply_symm_apply y)
  let c' : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V ∘ₗ c
  have hc' : ∀ y, (J (0, c y)).2 = c' y := fun _ => rfl
  let Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := Real.pi • (T ∘ₗ c)
  let Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := Real.pi • (T ∘ₗ c')
  have hQ : ∀ x y, Q x y = Real.pi * T y (c x) := fun x y => by rw [hT]; rfl
  have hQ' : ∀ x y, Q' x y = Real.pi * T y (c' x) := fun x y => by rw [hT]; rfl
  have s1 : ∀ x y, Q x y = Q y x := fun x y => by
    have := h1 (0, c x) (0, c y)
    simp only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply] at this
    rw [hQ, hQ]
    congr 1
    linarith
  have s2 : ∀ x y, Q' x y = Q' y x := fun x y => by
    have := h2 (0, c x) (0, c y)
    simp only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply] at this
    rw [hQ', hQ']
    congr 1
    linarith
  have pos : ∀ x, x ≠ 0 → 0 < Q x x := fun x hx => by
    have := h3 (0, c x) fun h => hx (by
      have := hc x
      rw [h, map_zero] at this
      exact neg_eq_zero.1 this.symm)
    simp only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply] at this
    rw [hQ]
    exact mul_pos Real.pi_pos (by linarith)
  obtain ⟨f, hf⟩ := exists_gauss Q Q' pos
  refine ⟨Q, Q', f, pos, hf, fun p x => ?_⟩
  have a1 := h1 p (0, c x)
  have a2 := h2 p (0, c x)
  simp only [om, hc, hc', map_neg, map_zero, LinearMap.neg_apply, LinearMap.zero_apply, sub_zero] at a1 a2
  rw [fderiv_gauss s1 s2 hf, fderiv_gauss s1 s2 hf, hQ, hQ, hQ', hQ', a1,
    show T (J p).1 (c' x) = T p.1 (c x) - T x (J p).2 by linarith]
  push_cast
  linear_combination ((2 * Real.pi) * f x * (T p.1 (c' x) + T x p.2 : ℂ)) * Complex.I_mul_I

end GlobalTheory.ThK.Dbl.Dense

end
