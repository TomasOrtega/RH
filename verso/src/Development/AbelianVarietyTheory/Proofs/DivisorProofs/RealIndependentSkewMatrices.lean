import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ r n G hG e he hF`. Establish `cc_mul' : ∀ x y : E, cc (x * y) = cc x * cc y` using `fun x y => map_mul (IsCMField.complexConj E) x y`. Establish `cc_add' : ∀ x y : E, cc (x + y) = cc x + cc y` using `fun x y => map_add (IsCMField.complexConj E) x y`. Establish `cc_cc' : ∀ x : E, cc (cc x) = x` using `fun x => IsCMField.complexConj_apply_apply E x`. Establish `hmap : ∀ g : Fin n → E, (∑ i, g i • e i).map cc = ∑ i, cc (g i) • (e i).map cc`.

Introduce `g`. Use extensionality with `a b`. Simplify using `[Matrix.sum_apply, cc, map_sum]`. Establish `hinj : ∀ M : Matrix (Fin r) (Fin r) E, Mᵀ * G = 0 → M = 0`. Introduce `M hM`.

Establish `hu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hG`. Establish `h0 : Mᵀ = 0`. Use `congrArg (· * G⁻¹) hM` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu]`. Simplify using `using congrArg Matrix.transpose h0`.

Establish `key : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∑ i, cc (g i) • e i = 0`. Introduce `g hg`. Apply `hinj` to reduce the goal to its premises. Establish `h2 : G * (∑ i, g i • e i).map cc = 0`. Rewrite using `[hg]`.

Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, cc]`. Rewrite `h2` using `[hmap, Finset.mul_sum]`. Establish `h3 : (∑ i, cc (g i) • e i)ᵀ * G = - ∑ i, G * (cc (g i) • (e i).map cc)`. Rewrite using `[Matrix.transpose_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]`. Use `congr 1`. Conclude with `eq_neg_of_add_eq_zero_left (he i)`. Rewrite using `[h3, h2, neg_zero]`.

Establish `real : ∀ g : Fin n → E, (∀ i, cc (g i) = g i) → ∑ i, g i • e i = 0 → ∀ i, g i = 0`. Introduce `g hc hg i`. Establish `hm : ∀ i, g i ∈ maximalRealSubfield E` using `fun i => (IsCMField.complexConj_eq_self_iff E _).mp (hc i)`. Use `Fintype.linearIndependent_iff.mp hF (fun i => ⟨g i, hm i⟩) hg i` as an intermediate fact. Simplify using `using congrArg (Subtype.val) this`.

Take `⟨x, hx⟩` from `DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)`. Establish `hx' : cc x ≠ x` using `hx`. Establish `sum_real : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∀ i, g i + cc (g i) = 0`. Introduce `g hg`. Apply `real` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[cc_add', cc_cc', add_comm]`. Simplify using `only [add_smul, Finset.sum_add_distrib, hg, key g hg, add_zero]`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`.

Establish `h1` using `sum_real g hg i`. Establish `hxg : ∑ i, (x * g i) • e i = 0`. Simplify using `only [mul_smul, ← Finset.smul_sum, hg, smul_zero]`. Establish `h2` using `sum_real (fun i => x * g i) hxg i`. Simplify using `only [cc_mul'] at h2`.

Establish `h3 : cc (g i) = - g i` using `eq_neg_of_add_eq_zero_right h1`. Rewrite `h2` using `[h3]`. Establish `h4 : (x - cc x) * g i = 0` using `by linear_combination h2`. Break down `mul_eq_zero.mp h4 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hx'`.

Conclude with `h`.
-/
theorem linearIndependent_of_skew_of_real : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 →
    ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) →
    LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  intro E _ _ _ r n G hG e he hF
  have cc_mul' : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add' : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc' : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x

  have hmap : ∀ g : Fin n → E, (∑ i, g i • e i).map cc = ∑ i, cc (g i) • (e i).map cc := by
    intro g
    ext a b
    simp [Matrix.sum_apply, cc, map_sum]
  have hinj : ∀ M : Matrix (Fin r) (Fin r) E, Mᵀ * G = 0 → M = 0 := by
    intro M hM
    have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
    have h0 : Mᵀ = 0 := by
      have := congrArg (· * G⁻¹) hM
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu] using this
    simpa using congrArg Matrix.transpose h0
  have key : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∑ i, cc (g i) • e i = 0 := by
    intro g hg
    apply hinj
    have h2 : G * (∑ i, g i • e i).map cc = 0 := by
      rw [hg]
      ext a b
      simp [Matrix.mul_apply, cc]
    rw [hmap, Finset.mul_sum] at h2
    have h3 : (∑ i, cc (g i) • e i)ᵀ * G = - ∑ i, G * (cc (g i) • (e i).map cc) := by
      rw [Matrix.transpose_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
      congr 1
      exact eq_neg_of_add_eq_zero_left (he i)
    rw [h3, h2, neg_zero]

  have real : ∀ g : Fin n → E, (∀ i, cc (g i) = g i) → ∑ i, g i • e i = 0 → ∀ i, g i = 0 := by
    intro g hc hg i
    have hm : ∀ i, g i ∈ maximalRealSubfield E := fun i =>
      (IsCMField.complexConj_eq_self_iff E _).mp (hc i)
    have := Fintype.linearIndependent_iff.mp hF (fun i => ⟨g i, hm i⟩) hg i
    simpa using congrArg (Subtype.val) this
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hx' : cc x ≠ x := hx

  have sum_real : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∀ i, g i + cc (g i) = 0 := by
    intro g hg
    apply real
    · intro i
      rw [cc_add', cc_cc', add_comm]
    · simp only [add_smul, Finset.sum_add_distrib, hg, key g hg, add_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := sum_real g hg i
  have hxg : ∑ i, (x * g i) • e i = 0 := by
    simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have h2 := sum_real (fun i => x * g i) hxg i
  simp only [cc_mul'] at h2
  have h3 : cc (g i) = - g i := eq_neg_of_add_eq_zero_right h1
  rw [h3] at h2
  have h4 : (x - cc x) * g i = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hx'
  · exact h

end GlobalTheory
