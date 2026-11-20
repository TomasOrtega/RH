import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

open Matrix

namespace GlobalTheory.HyperplaneSymmetricForm

/- English proof (translation)
Take `⟨⟨i0, hi0⟩, huniq⟩` from `Fintype.card_eq_one_iff.1 hs`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hUU : U * star U = 1` using `Unitary.coe_mul_star_self hA.eigenvectorUnitary`. Establish `hAe : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U`. Use `hA.spectral_theorem` as an intermediate fact.

Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `hne : ∀ i, hA.eigenvalues i ≠ 0`. Introduce `i hi`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[hA.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])`. Establish `hneg : ∀ i, i ≠ i0 → hA.eigenvalues i < 0`. Introduce `i hi`. Break down `lt_trichotomy (hA.eigenvalues i) 0 with h | h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h (hne i)`. Conclude with `absurd (congrArg Subtype.val (huniq ⟨i, h⟩)) hi`. Use `⟨(LinearMap.proj i0).comp (star U).mulVecLin, fun u hu hφ => ?_⟩` and prove the remaining obligations. Use `set c := star U *ᵥ u with hc`.

Establish `hφ' : c i0 = 0` using `hφ`. Establish `hc0 : c ≠ 0`. Introduce `h`. Apply `hu` to reduce the goal to its premises. Establish `: U *ᵥ c = u` using `by rw [hc, mulVec_mulVec, hUU, one_mulVec]`.

Rewrite using `[← this, h, mulVec_zero]`. Establish `hq : (star u ⬝ᵥ A *ᵥ u).re = ∑ i, hA.eigenvalues i * Complex.normSq (c i)`. Establish `e1 : star u ⬝ᵥ A *ᵥ u = star c ⬝ᵥ (diagonal (fun i => (hA.eigenvalues i : ℂ)) *ᵥ c)` using `by conv_lhs => rw [hAe]`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]`. Simplify using `[star_eq_conjTranspose]`.

Rewrite using `[e1, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mulVec_diagonal, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hq]`.

Take `⟨j, hj⟩` from `Function.ne_iff.1 hc0`. Establish `hj0 : j ≠ i0` using `by rintro rfl; exact hj hφ'`. Establish `: ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ)`. Use `Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = i0`.

Rewrite using `[h, hφ']`. Simplify using the standard rewrite rules. Conclude with `mul_nonpos_of_nonpos_of_nonneg (hneg i h).le (Complex.normSq_nonneg _)`. Conclude with `mul_neg_of_neg_of_pos (hneg j hj0) (Complex.normSq_pos.2 hj)`. Simplify using `using this`.
-/
theorem exists_hyperplane {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (hs : GlobalTheory.LKTrip.sigPosH hA = 1) :
    ∃ φ : (Fin n → ℂ) →ₗ[ℂ] ℂ, ∀ u, u ≠ 0 → φ u = 0 → (star u ⬝ᵥ A *ᵥ u).re < 0 := by
  obtain ⟨⟨i0, hi0⟩, huniq⟩ := Fintype.card_eq_one_iff.1 hs
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hAe : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hneg : ∀ i, i ≠ i0 → hA.eigenvalues i < 0 := by
    intro i hi
    rcases lt_trichotomy (hA.eigenvalues i) 0 with h | h | h
    · exact h
    · exact absurd h (hne i)
    · exact absurd (congrArg Subtype.val (huniq ⟨i, h⟩)) hi
  refine ⟨(LinearMap.proj i0).comp (star U).mulVecLin, fun u hu hφ => ?_⟩
  set c := star U *ᵥ u with hc
  have hφ' : c i0 = 0 := hφ
  have hc0 : c ≠ 0 := by
    intro h
    apply hu
    have : U *ᵥ c = u := by rw [hc, mulVec_mulVec, hUU, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : (star u ⬝ᵥ A *ᵥ u).re = ∑ i, hA.eigenvalues i * Complex.normSq (c i) := by
    have e1 : star u ⬝ᵥ A *ᵥ u = star c ⬝ᵥ (diagonal (fun i => (hA.eigenvalues i : ℂ)) *ᵥ c) := by
      conv_lhs => rw [hAe]
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
      simp [star_eq_conjTranspose]
    rw [e1, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mulVec_diagonal, Complex.normSq_apply]
    ring
  rw [hq]
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hc0
  have hj0 : j ≠ i0 := by rintro rfl; exact hj hφ'
  have : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · by_cases h : i = i0
      · rw [h, hφ']; simp
      · exact mul_nonpos_of_nonpos_of_nonneg (hneg i h).le (Complex.normSq_nonneg _)
    · exact mul_neg_of_neg_of_pos (hneg j hj0) (Complex.normSq_pos.2 hj)
  simpa using this

/- English proof (translation)
Establish `: star (star z ⬝ᵥ A *ᵥ x) = star x ⬝ᵥ A *ᵥ z`. Rewrite using `[← star_dotProduct_star, star_star, star_mulVec, hA.eq, ← dotProduct_mulVec]`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem form_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (x z : Fin n → ℂ) :
    star x ⬝ᵥ A *ᵥ z = (starRingEnd ℂ) (star z ⬝ᵥ A *ᵥ x) := by
  have : star (star z ⬝ᵥ A *ᵥ x) = star x ⬝ᵥ A *ᵥ z := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hA.eq, ← dotProduct_mulVec]
  rw [← this]; rfl

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_hyperplane A hA hd hs`. Establish `hz0 : z ≠ 0` using `by rintro rfl; simp at hz`. Establish `ha : φ z ≠ 0` using `fun h => absurd (hφ z hz0 h) (not_lt.2 hz.le)`. Establish `hzz` using `form_symm A hA z z`. Establish `hxx` using `form_symm A hA x x`.

Establish `hxz` using `form_symm A hA x z`. Use `set a := φ z with ha'`. Use `set b := φ x with hb'`. Establish `hu : φ (a • x - b • z) = 0`. Rewrite using `[map_sub, map_smul, map_smul, ← ha', ← hb', smul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hexp : star (a • x - b • z) ⬝ᵥ A *ᵥ (a • x - b • z) = (starRingEnd ℂ) a * a * (star x ⬝ᵥ A *ᵥ x) - (starRingEnd ℂ) a * b * (star x ⬝ᵥ A *ᵥ z) - (starRingEnd ℂ) b * a * (star z ⬝ᵥ A *ᵥ x) + (starRingEnd ℂ) b * b * (star z ⬝ᵥ A *ᵥ z)`. Simplify using `only [star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlin : star z ⬝ᵥ A *ᵥ (a • x - b • z) = a * (star z ⬝ᵥ A *ᵥ x) - b * (star z ⬝ᵥ A *ᵥ z)`.

Simplify using `only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Rewrite `hexp` using `[hxz]`. Generalize the expression as in `star z ⬝ᵥ A *ᵥ x = h at *`. Generalize the expression as in `star z ⬝ᵥ A *ᵥ z = P at *`. Generalize the expression as in `star x ⬝ᵥ A *ᵥ x = Q at *`.

Establish `hP : P.im = 0` using `Complex.conj_eq_iff_im.1 hzz.symm`. Establish `hQ : Q.im = 0` using `Complex.conj_eq_iff_im.1 hxx.symm`. Establish `hapos : 0 < Complex.normSq a` using `Complex.normSq_pos.2 ha`. Establish `key : P.re * (star (a • x - b • z) ⬝ᵥ A *ᵥ (a • x - b • z)).re = Complex.normSq a * (P.re * Q.re - Complex.normSq h) + Complex.normSq (a * h - b * P)`. Rewrite using `[hexp]`.

Simplify using `[Complex.normSq_apply, hP, hQ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Establish `hh` using `Complex.normSq_nonneg h`. Establish `hr` using `Complex.normSq_nonneg (a * h - b * P)`.

Distinguish the cases in `h0 : a • x - b • z = 0`. Rewrite `key`, `hlin` using `[h0]`. Simplify using `only [mulVec_zero, dotProduct_zero, Complex.zero_re, mul_zero] at key hlin`. Establish `hb : b ≠ 0`. Introduce `hb`.

Rewrite `h0` using `[hb, zero_smul, sub_zero]`. Conclude with `hx ((smul_eq_zero.1 h0).resolve_left ha)`. Establish `hP0 : P ≠ 0` using `by rintro rfl; simp at hz`. Establish `hh0 : h ≠ 0`. Introduce and unpack `rfl`.

Conclude with `mul_ne_zero hb hP0 (by linear_combination hlin)`. Establish `hpos` using `Complex.normSq_pos.2 hh0`. Establish `: P.re * Q.re - Complex.normSq h ≤ 0`. Assume the negation of the conclusion as `hc`. Use `mul_pos hapos (not_le.1 hc)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `mul_neg_of_pos_of_neg hz (hφ _ h0 hu)`. Establish `: P.re * Q.re - Complex.normSq h < 0`. Assume the negation of the conclusion as `hc`.

Use `mul_nonneg hapos.le (not_lt.1 hc)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (hs : GlobalTheory.LKTrip.sigPosH hA = 1) (z : Fin n → ℂ) (hz : 0 < (star z ⬝ᵥ A *ᵥ z).re)
    (x : Fin n → ℂ) (hx : x ≠ 0) :
    (star z ⬝ᵥ A *ᵥ z).re * (star x ⬝ᵥ A *ᵥ x).re < 2 * ‖star z ⬝ᵥ A *ᵥ x‖ ^ 2 := by
  obtain ⟨φ, hφ⟩ := exists_hyperplane A hA hd hs
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have ha : φ z ≠ 0 := fun h => absurd (hφ z hz0 h) (not_lt.2 hz.le)
  have hzz := form_symm A hA z z
  have hxx := form_symm A hA x x
  have hxz := form_symm A hA x z
  set a := φ z with ha'
  set b := φ x with hb'
  have hu : φ (a • x - b • z) = 0 := by
    rw [map_sub, map_smul, map_smul, ← ha', ← hb', smul_eq_mul, smul_eq_mul]; ring
  have hexp : star (a • x - b • z) ⬝ᵥ A *ᵥ (a • x - b • z) =
      (starRingEnd ℂ) a * a * (star x ⬝ᵥ A *ᵥ x) - (starRingEnd ℂ) a * b * (star x ⬝ᵥ A *ᵥ z)
       - (starRingEnd ℂ) b * a * (star z ⬝ᵥ A *ᵥ x) + (starRingEnd ℂ) b * b * (star z ⬝ᵥ A *ᵥ z) := by
    simp only [star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, RCLike.star_def]
    ring
  have hlin : star z ⬝ᵥ A *ᵥ (a • x - b • z) = a * (star z ⬝ᵥ A *ᵥ x) - b * (star z ⬝ᵥ A *ᵥ z) := by
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hxz] at hexp
  generalize star z ⬝ᵥ A *ᵥ x = h at *
  generalize star z ⬝ᵥ A *ᵥ z = P at *
  generalize star x ⬝ᵥ A *ᵥ x = Q at *
  have hP : P.im = 0 := Complex.conj_eq_iff_im.1 hzz.symm
  have hQ : Q.im = 0 := Complex.conj_eq_iff_im.1 hxx.symm
  have hapos : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  have key : P.re * (star (a • x - b • z) ⬝ᵥ A *ᵥ (a • x - b • z)).re =
      Complex.normSq a * (P.re * Q.re - Complex.normSq h) + Complex.normSq (a * h - b * P) := by
    rw [hexp]
    simp [Complex.normSq_apply, hP, hQ]
    ring
  rw [← Complex.normSq_eq_norm_sq]
  have hh := Complex.normSq_nonneg h
  have hr := Complex.normSq_nonneg (a * h - b * P)
  by_cases h0 : a • x - b • z = 0
  · rw [h0] at key hlin
    simp only [mulVec_zero, dotProduct_zero, Complex.zero_re, mul_zero] at key hlin
    have hb : b ≠ 0 := by
      intro hb
      rw [hb, zero_smul, sub_zero] at h0
      exact hx ((smul_eq_zero.1 h0).resolve_left ha)
    have hP0 : P ≠ 0 := by rintro rfl; simp at hz
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hb hP0 (by linear_combination hlin)
    have hpos := Complex.normSq_pos.2 hh0
    have : P.re * Q.re - Complex.normSq h ≤ 0 := by
      by_contra hc
      have := mul_pos hapos (not_le.1 hc)
      linarith
    linarith
  · have h1 := mul_neg_of_pos_of_neg hz (hφ _ h0 hu)
    have : P.re * Q.re - Complex.normSq h < 0 := by
      by_contra hc
      have := mul_nonneg hapos.le (not_lt.1 hc)
      linarith
    linarith

end GlobalTheory.HyperplaneSymmetricForm
