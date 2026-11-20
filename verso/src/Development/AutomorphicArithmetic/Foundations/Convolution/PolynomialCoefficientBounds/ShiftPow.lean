import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro q`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `q`. Establish `h1 : (LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) - Complex.exp c • (1 : Module.End ℂ (ℂ → ℂ))) (fun t => q t * Complex.exp (c * t)) = Complex.exp c • fun t => fwdDiff (1 : ℂ) q t * Complex.exp (c * t)`. Use function extensionality and compare the values at `t`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, fwdDiff, mul_add, mul_one, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[pow_succ, Module.End.mul_apply, h1, map_smul, ih]`. Use function extensionality and compare the values at `t`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Function.iterate_succ_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma shift_pow (c : ℂ) (k : ℕ) : ∀ (q : ℂ → ℂ),
    ((LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) - Complex.exp c • (1 : Module.End ℂ (ℂ → ℂ))) ^ k)
      (fun t => q t * Complex.exp (c * t)) =
      fun t => Complex.exp c ^ k * ((fwdDiff (1 : ℂ))^[k] q t * Complex.exp (c * t)) := by
  induction k with
  | zero => intro q; funext t; simp
  | succ k ih =>
    intro q
    have h1 : (LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) - Complex.exp c • (1 : Module.End ℂ (ℂ → ℂ)))
        (fun t => q t * Complex.exp (c * t)) =
        Complex.exp c • fun t => fwdDiff (1 : ℂ) q t * Complex.exp (c * t) := by
      funext t
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
        Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, fwdDiff, mul_add, mul_one, Complex.exp_add]
      ring
    rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih]
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, Function.iterate_succ_apply]
    ring

/- English proof (translation)
Establish `hinj : Function.Injective fun a => Complex.exp (c a)`. Introduce `a b hab`. Apply `hc` to reduce the goal to its premises. Apply `Real.exp_injective` to reduce the goal to its premises. Simplify using `only [← Complex.ofReal_exp] at hab`.

Conclude with `hab` after adjusting the coercions. Establish `hind` using `(Module.End.independent_maxGenEigenspace (LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) : Module.End ℂ (ℂ → ℂ))).comp hinj`. Rewrite `hind` using `[iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]`. Use `hind Finset.univ (fun a t => (q a).eval t * Complex.exp (c a * t)) ?_ ?_ a (Finset.mem_univ a)` as an intermediate fact. Simplify using `using congrFun this 0`.

Introduce `b _`. Rewrite using `[Function.comp_apply, Module.End.mem_maxGenEigenspace]`. Use `⟨(q b).natDegree + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[shift_pow (c b) _ (fun t => (q b).eval t), Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (Nat.lt_succ_self _)]`. Use function extensionality and compare the values at `t`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `t`. Simplify `h t` using `[Finset.sum_apply]`.
-/
private lemma one_var {α : Type} [Fintype α] (c : α → ℝ) (hc : Function.Injective c)
    (q : α → Polynomial ℂ) (h : ∀ t : ℂ, ∑ a, (q a).eval t * Complex.exp (c a * t) = 0) (a : α) :
    (q a).eval 0 = 0 := by
  have hinj : Function.Injective fun a => Complex.exp (c a) := by
    intro a b hab
    apply hc
    apply Real.exp_injective
    simp only [← Complex.ofReal_exp] at hab
    exact_mod_cast hab
  have hind := (Module.End.independent_maxGenEigenspace
    (LinearMap.funLeft ℂ ℂ (fun t : ℂ => t + 1) : Module.End ℂ (ℂ → ℂ))).comp hinj
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hind
  have := hind Finset.univ (fun a t => (q a).eval t * Complex.exp (c a * t)) ?_ ?_ a (Finset.mem_univ a)
  · simpa using congrFun this 0
  · intro b _
    rw [Function.comp_apply, Module.End.mem_maxGenEigenspace]
    refine ⟨(q b).natDegree + 1, ?_⟩
    rw [shift_pow (c b) _ (fun t => (q b).eval t),
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (Nat.lt_succ_self _)]
    funext t
    simp
  · funext t
    simpa [Finset.sum_apply] using h t

/- English proof (translation)
Use `conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `AddMonoidAlgebra.liftNC _ _ (AddMonoidAlgebra.single v _) = _`. Rewrite using `[AddMonoidAlgebra.liftNC_single]`. Both sides reduce to the same expression.
-/
private lemma ev_eq {ι : Type} [Fintype ι] (f : EP ι) (Λ : ι → ℂ) :
    ev Λ f = ∑ v ∈ f.coeff.support, eval Λ (f.coeff v) * Complex.exp (∑ i, (v i : ℂ) * Λ i) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  change AddMonoidAlgebra.liftNC _ _ (AddMonoidAlgebra.single v _) = _
  rw [AddMonoidAlgebra.liftNC_single]
  rfl

/- English proof (translation)
Take `⟨u, hu⟩` from `Module.Dual.exists_forall_ne_zero_of_forall_exists (K := ℝ) (M := ι → ℝ) (ι := {p : s × s // p.1 ≠ p.2}) (fun p => ∑ i, (p.1.1.1 i - p.1.2.1 i) • LinearMap.proj i) (by`. Introduce and unpack `⟨⟨v, w⟩, hvw⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, v.1 i ≠ w.1 i := by`. Assume the negation of the conclusion as `hh`. Use `push Not at hh`.

Conclude with `hvw (Subtype.ext (funext hh))`. Use `⟨Pi.single i 1, ?_⟩` and prove the remaining obligations. Simplify using `[LinearMap.sum_apply, Pi.single_apply, sub_eq_zero, hi])`. Use `⟨u, fun v w hvw => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Apply `hu ⟨(v, w), hne⟩` to reduce the goal to its premises. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]`. Conclude with `sub_eq_zero.2 hvw`.
-/
private lemma generic {ι : Type} [Fintype ι] (s : Finset (ι → ℝ)) :
    ∃ u : ι → ℝ, Function.Injective fun v : s => ∑ i, v.1 i * u i := by
  classical
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (K := ℝ) (M := ι → ℝ)
    (ι := {p : s × s // p.1 ≠ p.2})
    (fun p => ∑ i, (p.1.1.1 i - p.1.2.1 i) • LinearMap.proj i) (by
      rintro ⟨⟨v, w⟩, hvw⟩
      obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ w.1 i := by
        by_contra hh
        push Not at hh
        exact hvw (Subtype.ext (funext hh))
      refine ⟨Pi.single i 1, ?_⟩
      simp [LinearMap.sum_apply, Pi.single_apply, sub_eq_zero, hi])
  refine ⟨u, fun v w hvw => ?_⟩
  by_contra hne
  apply hu ⟨(v, w), hne⟩
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hvw

/- English proof (translation)
Introduce `ι _ f hf`. Take `⟨u, hu⟩` from `generic f.coeff.support`. Rewrite using `[← AddMonoidAlgebra.coeff_eq_zero]`. Use `ext1 v`. Assume the negation of the conclusion as `hv`.

Apply `hv` to reduce the goal to its premises. Establish `hv' : v ∈ f.coeff.support` using `Finsupp.mem_support_iff.2 hv`. Use `MvPolynomial.funext fun Λ => ?_` and prove the remaining obligations. Establish `hev : ∀ (p : MvPolynomial ι ℂ) (t : ℂ), Polynomial.eval t (aeval (fun i => Polynomial.C (Λ i) + Polynomial.C (u i : ℂ) * Polynomial.X) p) = eval (fun i => Λ i + (u i : ℂ) * t) p`. Introduce `p t`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => simp [hp]`. Establish `key` using `one_var _ hu (fun w : f.coeff.support => Polynomial.C (Complex.exp (∑ i, (w.1 i : ℂ) * Λ i)) * aeval (fun i => Polynomial.C (Λ i) + Polynomial.C (u i : ℂ) * Polynomial.X) (f.coeff w.1)) ?_ ⟨v, hv'⟩`.

Rewrite `key` using `[Polynomial.eval_mul, hev, Polynomial.eval_C]`. Simplify using `using key`. Introduce `t`. Use `hf (fun i => Λ i + (u i : ℂ) * t)` as an intermediate fact. Rewrite `this` using `[ev_eq, ← Finset.sum_coe_sort]`.

Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.eval_mul, hev, Polynomial.eval_C]`. Establish `: ∑ i, (w.1 i : ℂ) * (Λ i + (u i : ℂ) * t) = ∑ i, (w.1 i : ℂ) * Λ i + ((∑ i, w.1 i * u i : ℝ) : ℂ) * t`. Use `push_cast`.

Simplify using `only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]`. Rewrite using `[this, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.FX.ev_inj :
    ∀ (ι : Type) [Fintype ι] (f : EP ι), (∀ Λ : ι → ℂ, ev Λ f = 0) → f = 0 := by
  intro ι _ f hf
  obtain ⟨u, hu⟩ := generic f.coeff.support
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  ext1 v
  by_contra hv
  apply hv
  have hv' : v ∈ f.coeff.support := Finsupp.mem_support_iff.2 hv
  refine MvPolynomial.funext fun Λ => ?_
  have hev : ∀ (p : MvPolynomial ι ℂ) (t : ℂ),
      Polynomial.eval t (aeval (fun i => Polynomial.C (Λ i) + Polynomial.C (u i : ℂ) * Polynomial.X) p) =
        eval (fun i => Λ i + (u i : ℂ) * t) p := by
    intro p t
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have key := one_var _ hu (fun w : f.coeff.support =>
    Polynomial.C (Complex.exp (∑ i, (w.1 i : ℂ) * Λ i)) *
      aeval (fun i => Polynomial.C (Λ i) + Polynomial.C (u i : ℂ) * Polynomial.X) (f.coeff w.1)) ?_ ⟨v, hv'⟩
  · rw [Polynomial.eval_mul, hev, Polynomial.eval_C] at key
    simpa using key
  · intro t
    have := hf (fun i => Λ i + (u i : ℂ) * t)
    rw [ev_eq, ← Finset.sum_coe_sort] at this
    rw [← this]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Polynomial.eval_mul, hev, Polynomial.eval_C]
    have : ∑ i, (w.1 i : ℂ) * (Λ i + (u i : ℂ) * t) =
        ∑ i, (w.1 i : ℂ) * Λ i + ((∑ i, w.1 i * u i : ℝ) : ℂ) * t := by
      push_cast
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    rw [this, Complex.exp_add]
    ring
