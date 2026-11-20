import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.NormMono

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

/- English proof (translation)
The claim follows from `GI.integP`.
-/
theorem integP : IntegP := GI.integP

/- English proof (translation)
Set `L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)` to `((ζ • LinearMap.id : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ))).restrictScalars ℝ`. Establish `hdet : LinearMap.det L = 1`. Simplify using `only [L]`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one, Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, hζ]`. Simplify using the standard rewrite rules.

Use `haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ))) (f := L) (by rw [hdet]; exact one_ne_zero)` as an intermediate fact. Rewrite `this` using `[hdet]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma map_smul_volume {m n : ℕ} (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = volume := by
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    ((ζ • LinearMap.id : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ))).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, hζ]
    simp
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at this
  calc Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = Measure.map (⇑L) volume := rfl
    _ = volume := by rw [this]; simp

/- English proof (translation)
Unfold `evX`. Rewrite using `[MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk2 : k.2.2 = false`. Assume the negation of the conclusion as `h`.

Conclude with `(Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))`. Simplify using `[hk2, mul_pow]`.
-/
lemma evX_smul_mono {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by
  unfold evX
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk2 : k.2.2 = false := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))
  simp [hk2, mul_pow]

/- English proof (translation)
Unfold `gs`. Simplify using `[hζ]`.
-/
lemma gs_smul {m n : ℕ} (c : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) : gs c (ζ • x) = gs c x := by
  unfold gs
  simp [hζ]

/- English proof (translation)
Establish `h1 : (starRingEnd ℂ) ζ * ζ = 1`. Rewrite using `[← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]`. Simplify using the standard rewrite rules. Establish `key : ∀ u v : ℂ, (starRingEnd ℂ) (ζ * u) * (ζ * v) = (starRingEnd ℂ) u * v`. Introduce `u v`.

Rewrite using `[map_mul]`. Take the linear combination `((starRingEnd ℂ) u * v) * h1`. Use extensionality with `_i _j`. Simplify using `only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>`.

Apply the tactic sequence `simp only [Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, if_true, if_false] <;>`. Conclude with `key _ _`.
-/
lemma gramX_smul {m n : ℕ} (ε : Fin m → Bool) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) :
    gramX ε (ζ • x) = gramX ε x := by
  have h1 : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]; simp
  have key : ∀ u v : ℂ, (starRingEnd ℂ) (ζ * u) * (ζ * v) = (starRingEnd ℂ) u * v := by
    intro u v
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) u * v) * h1
  ext _i _j
  simp only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    simp only [Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, if_true, if_false] <;>
    exact key _ _

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _`.
-/
lemma continuous_gramX {m n : ℕ} (ε : Fin m → Bool) : Continuous fun x : Fin m → Fin n → ℂ => gramX ε x :=
  continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _

/- English proof (translation)
Introduce `m n ε c t hc b hb d hd hd0`. Use `set N := d.sum fun _ e => e with hN`. Establish `hN0 : N ≠ 0`. Introduce `h`. Apply `hd0` to reduce the goal to its premises.

Use extensionality with `k`. Use `(Finset.sum_eq_zero_iff.mp h) k` as an intermediate fact. Distinguish the cases in `hk : k ∈ d.support`. Simplify using `using this hk`. Simplify using `using hk`.

Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN0`. Use `set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef`. Establish `hζ : ‖ζ‖ = 1` using `by rw [hζdef, Complex.norm_exp_ofReal_mul_I]`. Establish `hζN : ζ ^ N = -1`. Rewrite using `[hζdef, ← Complex.exp_nat_mul]`.

Establish `: (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.exp_pi_mul_I]`. Set `F : (Fin m → Fin n → ℂ) → ℂ` to `fun x => evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)`.

Establish `hcont : Continuous F` using `((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))`. Establish `hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x`. Use function extensionality and compare the values at `x`. Simplify using `only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : ∫ x, F (ζ • x) = ∫ x, F x`. Rewrite using `[← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x) (continuous_const_smul ζ).measurable.aemeasurable (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]`. Establish `h2 : ∫ x, F x = -∫ x, F x` using `by conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]`. Use `show ∫ x, F x = 0`. Take the linear combination `(1 / 2 : ℂ) * h2`.
-/
theorem rot : Rot := by
  intro m n ε c t hc b hb d hd hd0
  set N := d.sum fun _ e => e with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hd0
    ext k
    have := (Finset.sum_eq_zero_iff.mp h) k
    by_cases hk : k ∈ d.support
    · simpa using this hk
    · simpa using hk
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp_ofReal_mul_I]
  have hζN : ζ ^ N = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  let F : (Fin m → Fin n → ℂ) → ℂ := fun x =>
    evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
  have hcont : Continuous F :=
    ((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp
      (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))
  have hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x := by
    funext x
    simp only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]
    ring
  have hint : ∫ x, F (ζ • x) = ∫ x, F x := by
    rw [← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x)
      (continuous_const_smul ζ).measurable.aemeasurable
      (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]
  have h2 : ∫ x, F x = -∫ x, F x := by
    conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]
  show ∫ x, F x = 0
  linear_combination (1 / 2 : ℂ) * h2

end PositivityTheory.Rg.Sw.WR.G
