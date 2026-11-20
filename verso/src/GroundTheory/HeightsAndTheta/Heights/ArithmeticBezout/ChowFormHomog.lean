import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum]`. Use `conv_rhs => rw [p.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Establish `hw : ∑ j ∈ d.support, w j * d j = a`. Rewrite using `[← hp (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]`. Simplify using `[smul_eq_mul, mul_comm]`.

Rewrite using `[hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_scale_of_isWeightedHomogeneous {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {w : σ → ℕ} {p : MvPolynomial σ R} {a : ℕ} (hp : IsWeightedHomogeneous w p a)
    (t : A) (u : σ → A) : aeval (fun j => t ^ w j * u j) p = t ^ a * aeval u p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hw : ∑ j ∈ d.support, w j * d j = a := by
    rw [← hp (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul, mul_comm]
  rw [hw]
  ring

variable {F : Type} [Field F] {n k : ℕ}

/- English proof (translation)
Take `⟨x, hx0, hxI, hux⟩` from `hu`. Use `⟨x, hx0, hxI, fun i' => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ j : Fin n, t ^ inGroup i (i', j) * u (i', j) * x j = t ^ (if i' = i then 1 else 0) * (u (i', j) * x j)` using `fun j => by rw [mul_assoc]; rfl`. Use `Eq.trans (Finset.sum_congr rfl fun j _ => hc j) ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, hux i', mul_zero]`.
-/
theorem scale_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence I k) (i : Fin k)
    (t : AlgebraicClosure F) : (fun ij => t ^ inGroup i ij * u ij) ∈ incidence I k := by
  obtain ⟨x, hx0, hxI, hux⟩ := hu
  refine ⟨x, hx0, hxI, fun i' => ?_⟩
  have hc : ∀ j : Fin n, t ^ inGroup i (i', j) * u (i', j) * x j =
      t ^ (if i' = i then 1 else 0) * (u (i', j) * x j) := fun j => by rw [mul_assoc]; rfl
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hc j) ?_
  rw [← Finset.mul_sum, hux i', mul_zero]

/- English proof (translation)
Introduce `u hu`. Use `set w := inGroup (n := n) i`. Use `set S := weightSet w f`. Use `set q : Polynomial (AlgebraicClosure F) := ∑ b ∈ S, Polynomial.C (aeval u (weightedHomogeneousComponent w b f)) * Polynomial.X ^ b with hq_def`. Establish `hq : q = 0`.

Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `t`. Establish `h1` using `hf _ (scale_mem_incidence hu i t)`. Rewrite `h1` using `[← sum_weightSet_component (w := w) f, map_sum]`. Simplify using `only [hq_def, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[aeval_scale_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous b f), mul_comm]`. Establish `hc` using `congrArg (fun p => Polynomial.coeff p a) hq`. Simplify using `only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc`.

Rewrite `hc` using `[Finset.sum_ite_eq, if_pos ha]`. Conclude with `hc`.
-/
theorem component_vanish_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : ∀ u ∈ incidence I k, aeval u f = 0) (i : Fin k)
    {a : ℕ} (ha : a ∈ weightSet (inGroup (n := n) i) f) :
    ∀ u ∈ incidence I k, aeval u (weightedHomogeneousComponent (inGroup (n := n) i) a f) = 0 := by
  classical
  intro u hu
  set w := inGroup (n := n) i
  set S := weightSet w f
  set q : Polynomial (AlgebraicClosure F) :=
    ∑ b ∈ S, Polynomial.C (aeval u (weightedHomogeneousComponent w b f)) * Polynomial.X ^ b with hq_def
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have h1 := hf _ (scale_mem_incidence hu i t)
    rw [← sum_weightSet_component (w := w) f, map_sum] at h1
    simp only [hq_def, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aeval_scale_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous b f),
      mul_comm]
  have hc := congrArg (fun p => Polynomial.coeff p a) hq
  simp only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq, if_pos ha] at hc
  exact hc

/- English proof (translation)
Take `⟨a, ha⟩` from `weightSet_nonempty (w := inGroup (n := n) i) hf.1`. Establish `hvan : ∀ u ∈ incidence I k, aeval u f = 0` using `(hf.2 f).mpr dvd_rfl`. Take `⟨r, hr⟩` from `(hf.2 _).mp (component_vanish_incidence hvan i ha)`. Establish `hc` using `component_ne_zero_of_mem ha`. Rewrite `hc` using `[hr]`.

Use `isWeightedHomogeneous_of_mul_left (m := a) ?_ hf.1 (right_ne_zero_of_mul hc)` and prove the remaining obligations. Rewrite using `[← hr]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous a f`.
-/
theorem IsChowForm.exists_isWeightedHomogeneous_inGroup {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup (n := n) i) f a := by
  obtain ⟨a, ha⟩ := weightSet_nonempty (w := inGroup (n := n) i) hf.1
  have hvan : ∀ u ∈ incidence I k, aeval u f = 0 := (hf.2 f).mpr dvd_rfl
  obtain ⟨r, hr⟩ := (hf.2 _).mp (component_vanish_incidence hvan i ha)
  have hc := component_ne_zero_of_mem ha
  rw [hr] at hc
  refine isWeightedHomogeneous_of_mul_left (m := a) ?_ hf.1 (right_ne_zero_of_mul hc)
  rw [← hr]
  exact weightedHomogeneousComponent_isWeightedHomogeneous a f

/- English proof (translation)
Take `⟨j, hj⟩` from `hP.isRelevant`. Establish `hex : ∃ x ∈ zeroLocus (AlgebraicClosure F) P, x ≠ 0`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hj` to reduce the goal to its premises.

Establish `hrad : X j ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) P)`. Rewrite using `[mem_vanishingIdeal_iff]`. Introduce `x hx`. Rewrite using `[h x hx]`. Simplify using the standard rewrite rules.

Rewrite `hrad` using `[vanishingIdeal_zeroLocus_eq_radical, hP.isPrime.radical]`. Then use the resulting hypothesis. Take `⟨x, hx, hx0⟩` from `hex`. Conclude with `⟨x, hx0, fun g hg => mem_zeroLocus_iff.mp hx g hg, fun i => by simp⟩`.
-/
theorem zero_mem_incidence {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) (k : ℕ) :
    (0 : Fin k × Fin n → AlgebraicClosure F) ∈ incidence P k := by
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hex : ∃ x ∈ zeroLocus (AlgebraicClosure F) P, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    have hrad : X j ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) P) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [h x hx]
      simp
    rwa [vanishingIdeal_zeroLocus_eq_radical, hP.isPrime.radical] at hrad
  obtain ⟨x, hx, hx0⟩ := hex
  exact ⟨x, hx0, fun g hg => mem_zeroLocus_iff.mp hx g hg, fun i => by simp⟩

/- English proof (translation)
Break down `Nat.eq_zero_or_pos k with hk0 | hk` into its components or cases. Substitute `hk0` using the available equality. Conclude with `⟨1, le_rfl, fun d _ => funext fun i => i.elim0⟩`. Use `choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i`. Establish `hδ : IsMultiHomog (a ⟨0, hk⟩) f` using `(isMultiHomog_iff _ _).mpr fun i => by`.

Rewrite using `[hf.degrees_eq ha ⟨0, hk⟩ i]`. Conclude with `ha i`. Use `⟨a ⟨0, hk⟩, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hδ⟩` and prove the remaining obligations. Rewrite `hδ` using `[h0]`. Establish `hd0 : ∀ d ∈ f.support, d = 0`.

Introduce `d hd`. Establish `h` using `congrFun (hδ (mem_support_iff.mp hd))`. Use extensionality with `ij`. Assume the negation of the conclusion as `hne`. Establish `h1` using `h ij.1`.

Rewrite `h1` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Establish `h2` using `(Finset.sum_eq_zero_iff.mp h1) ij (Finsupp.mem_support_iff.mpr hne)`. Simplify using `[groupWeight] at h2`. Conclude with `hne h2`. Establish `hC : f = C (coeff 0 f)`.

Use extensionality with `d`. Rewrite using `[coeff_C]`. Use `split_ifs with hd`. Rewrite using `[hd]`. Assume the negation of the conclusion as `hne`.

Conclude with `hd (hd0 d (mem_support_iff.mpr hne)).symm`. Establish `hz` using `(hf.2 f).mpr dvd_rfl 0 (zero_mem_incidence hP k)`. Rewrite `hz` using `[hC, aeval_C, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective]`. Conclude with `hf.1 (by rw [hC, hz, C_0])`.
-/
theorem IsChowForm.exists_multiHomog {P : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hP : IsProjPrime P) (hf : IsChowForm P k f) :
    ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨1, le_rfl, fun d _ => funext fun i => i.elim0⟩
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  refine ⟨a ⟨0, hk⟩, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hδ⟩
  rw [h0] at hδ
  have hd0 : ∀ d ∈ f.support, d = 0 := by
    intro d hd
    have h := congrFun (hδ (mem_support_iff.mp hd))
    ext ij
    by_contra hne
    have h1 := h ij.1
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
    have h2 := (Finset.sum_eq_zero_iff.mp h1) ij (Finsupp.mem_support_iff.mpr hne)
    simp [groupWeight] at h2
    exact hne h2
  have hC : f = C (coeff 0 f) := by
    ext d
    rw [coeff_C]
    split_ifs with hd
    · rw [hd]
    · by_contra hne
      exact hd (hd0 d (mem_support_iff.mpr hne)).symm
  have hz := (hf.2 f).mpr dvd_rfl 0 (zero_mem_incidence hP k)
  rw [hC, aeval_C, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective] at hz
  exact hf.1 (by rw [hC, hz, C_0])

/- English proof (translation)
The claim follows from `(isChowForm_point ℚ).exists_multiHomog (isProjPrime_point ℚ)`.
-/
example : ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) :=
  (isChowForm_point ℚ).exists_multiHomog (isProjPrime_point ℚ)

end

end GroundTheory.Heights₂.Heights
