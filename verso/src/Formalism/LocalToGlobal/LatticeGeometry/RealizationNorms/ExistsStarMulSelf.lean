import Mathlib

open Matrix
open scoped ComplexOrder

namespace Formalism.L2.Geo.Rec.TraceQuadraticBound

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `open scoped MatrixOrder in`. Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg`. Conclude with `⟨B, hB⟩`.
-/
theorem exists_star_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, hB⟩

/- English proof (translation)
Take `⟨B, rfl⟩` from `exists_star_mul_self hA`. Use `⟨Bᴴ, by rw [conjTranspose_conjTranspose], ?_⟩` and prove the remaining obligations. Rewrite `hd` using `[det_mul]`. Conclude with `isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd)`.
-/
theorem frame_exists {A : Matrix n n ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) :
    ∃ X : Matrix n n ℂ, X * Xᴴ = A ∧ IsUnit X.det := by
  obtain ⟨B, rfl⟩ := exists_star_mul_self hA
  refine ⟨Bᴴ, by rw [conjTranspose_conjTranspose], ?_⟩
  rw [det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd)

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.
-/
theorem re_star_dot_self (v : n → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/- English proof (translation)
Establish `h1 : ‖∑ k, a k * w k‖ ≤ ∑ k, ‖a k‖ * ‖w k‖` using `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖w k‖)`. Establish `h0 : 0 ≤ ‖∑ k, a k * w k‖` using `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sum_sq_le (a w : n → ℂ) : ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖w k‖ ^ 2 := by
  have h1 : ‖∑ k, a k * w k‖ ≤ ∑ k, ‖a k‖ * ‖w k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖w k‖)
  have h0 : 0 ≤ ‖∑ k, a k * w k‖ := norm_nonneg _
  calc ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖w k‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

/- English proof (translation)
Establish `e1 : star w ⬝ᵥ (Hᴴ * H) *ᵥ w = star (H *ᵥ w) ⬝ᵥ (H *ᵥ w)`. Rewrite using `[← mulVec_mulVec, dotProduct_mulVec, star_mulVec]`. Rewrite using `[e1, re_star_dot_self]`. Establish `e2 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2`. Simplify using `only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`. Rewrite using `[e2, Finset.sum_comm, Finset.sum_mul]`. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations.

Conclude with `norm_sum_sq_le (fun j => H k j) w`.
-/
theorem quad_le_trace_HH (H : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ (Hᴴ * H) *ᵥ w).re ≤ (Hᴴ * H).trace.re * ∑ i, ‖w i‖ ^ 2 := by
  have e1 : star w ⬝ᵥ (Hᴴ * H) *ᵥ w = star (H *ᵥ w) ⬝ᵥ (H *ᵥ w) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  rw [e1, re_star_dot_self]
  have e2 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  exact norm_sum_sq_le (fun j => H k j) w

/- English proof (translation)
Take `⟨H, hH⟩` from `exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)`. Establish `e1 : star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w) = star w ⬝ᵥ (Yᴴ * b * Y) *ᵥ w`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Establish `e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace`. Rewrite using `[← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]`.

Rewrite using `[e1, e2, hH]`. Conclude with `quad_le_trace_HH H w`.
-/
theorem quad_le_trace {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) (w : n → ℂ) :
    (star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w)).re ≤ (b * (Y * Yᴴ)).trace.re * ∑ i, ‖w i‖ ^ 2 := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e1 : star (Y *ᵥ w) ⬝ᵥ b *ᵥ (Y *ᵥ w) = star w ⬝ᵥ (Yᴴ * b * Y) *ᵥ w := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e1, e2, hH]
  exact quad_le_trace_HH H w

/- English proof (translation)
Take `⟨H, hH⟩` from `exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)`. Establish `e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace`. Rewrite using `[← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]`. Rewrite using `[e2, hH]`. Simplify using `only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`.

Use `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`. Check the signs of the components of the expression.
-/
theorem trace_nonneg {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) :
    0 ≤ (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e2, hH]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity

/- English proof (translation)
Take `⟨H, hH⟩` from `exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)`. Establish `e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace`. Rewrite using `[← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]`. Establish `e3 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2`. Simplify using `only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`. Rewrite using `[e2, hH, e3]`. Assume the negation of the conclusion as `hle`.

Establish `hs : ∑ j, ∑ k, ‖H k j‖ ^ 2 = 0` using `le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity)`. Establish `hH0 : H = 0`. Use extensionality with `k j`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => by positivity)).1 hs j (Finset.mem_univ _)`. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h1 k (Finset.mem_univ _)`.

Simplify using `using h2`. Apply `hb0` to reduce the goal to its premises. Establish `hYi : IsUnit Yᴴ.det` using `by rw [det_conjTranspose]; exact hY.star`. Establish `hz : Yᴴ * b * Y = 0` using `by rw [hH, hH0]; simp`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.nonsing_inv_mul _ hYi, Matrix.mul_nonsing_inv _ hY]`. Simplify using the standard rewrite rules. Use `_ = Yᴴ⁻¹ * (Yᴴ * b * Y) * Y⁻¹ := by simp only [Matrix.mul_assoc]`. Use `_ = 0 := by rw [hz]; simp`.
-/
theorem trace_pos {b : Matrix n n ℂ} (hb : b.PosSemidef) (hb0 : b ≠ 0) (Y : Matrix n n ℂ)
    (hY : IsUnit Y.det) : 0 < (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have e3 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, hH, e3]
  by_contra hle
  have hs : ∑ j, ∑ k, ‖H k j‖ ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity)
  have hH0 : H = 0 := by
    ext k j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => by positivity)).1 hs j
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h1 k (Finset.mem_univ _)
    simpa using h2
  apply hb0
  have hYi : IsUnit Yᴴ.det := by rw [det_conjTranspose]; exact hY.star
  have hz : Yᴴ * b * Y = 0 := by rw [hH, hH0]; simp
  calc b = (Yᴴ⁻¹ * Yᴴ) * b * (Y * Y⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hYi, Matrix.mul_nonsing_inv _ hY]; simp
    _ = Yᴴ⁻¹ * (Yᴴ * b * Y) * Y⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp

section Dense

variable {K : Type} [Field K]

/- English proof (translation)
Set `g : ℝ × ℝ → ℂ` to `fun p => (p.1 : ℂ) + (p.2 : ℂ) * σ z`. Establish `hg : Continuous g` using `by fun_prop`. Establish `hgs : Function.Surjective g`. Introduce `w`. Use `⟨(w.re - w.im / (σ z).im * (σ z).re, w.im / (σ z).im), ?_⟩` and prove the remaining obligations.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[g]`. Simplify using `[g]`. Clear the denominators using the available nonvanishing facts. Establish `hq : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ)))` using `Rat.denseRange_cast.prodMap Rat.denseRange_cast`.

Establish `h` using `hgs.denseRange.comp hq hg`. Use `h.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨a, b⟩, rfl⟩`. Conclude with `⟨(a : K) + (b : K) * z, by simp [g]⟩`.
-/
theorem denseRange_emb (σ : K →+* ℂ) (z : K) (hz : (σ z).im ≠ 0) : DenseRange σ := by
  let g : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * σ z
  have hg : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    intro w
    refine ⟨(w.re - w.im / (σ z).im * (σ z).re, w.im / (σ z).im), ?_⟩
    apply Complex.ext
    · simp [g]
    · simp [g]; field_simp
  have hq : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h := hgs.denseRange.comp hq hg
  refine h.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(a : K) + (b : K) * z, by simp [g]⟩

/- English proof (translation)
Establish `hHm : (A.map σ).IsHermitian`. Use extensionality with `i k`. Simplify using `only [conjTranspose_apply, map_apply]`. Rewrite using `[hH, hσ, star_star]`. Establish `key : ∀ l : Fin m → K, σ (∑ i, ∑ k, l i * A i k * cj (l k)) = star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k)))`.

Introduce `l`. Simplify using `only [map_sum, map_mul, hσ, dotProduct, mulVec, map_apply, Pi.star_apply, star_star, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations. Establish `hden : DenseRange (fun l : Fin m → K => fun k => star (σ (l k)))`. Establish `h1 : DenseRange (fun z : K => star (σ z))` using `(Function.RightInverse.surjective (f := (star : ℂ → ℂ)) (g := star) star_star).denseRange.comp hd continuous_star`.

Conclude with `DenseRange.piMap (f := fun _ : Fin m => fun z : K => star (σ z)) (fun _ => h1)`. Establish `hre : ∀ x : Fin m → ℂ, 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re`. Introduce `x`. Use `hden.induction_on (p := fun x => 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re) x ?_ ?_` and prove the remaining obligations. Apply `isClosed_le continuous_const` to reduce the goal to its premises.

Simplify using `only [dotProduct, mulVec, Pi.star_apply]`. Use `fun_prop`. Introduce `l show 0 ≤ (star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k)))).re`. Distinguish the cases in `hl : l = 0`. Substitute `hl` using the available equality.

Rewrite using `[show (fun k : Fin m => star (σ ((0 : Fin m → K) k))) = 0 by funext k; simp]`. Simplify using the standard rewrite rules. Rewrite using `[← key]`. Conclude with `(hP l hl).le`. Use `⟨PosSemidef.of_dotProduct_mulVec_nonneg hHm fun x => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Complex.nonneg_iff]`. Conclude with `⟨hre x, (hHm.im_star_dotProduct_mulVec_self x).symm⟩`. Rewrite using `[show (A.map σ).det = σ A.det from (RingHom.map_det σ A).symm]`. Introduce `h0`. Apply `(map_eq_zero_iff σ σ.injective).not.mpr ?_ h0` to reduce the goal to its premises.

Introduce `hdet`. Take `⟨l, hl, hlA⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hdet`. Use `hP l hl` as an intermediate fact. Establish `e : ∑ i, ∑ k, l i * A i k * cj (l k) = ∑ k, (l ᵥ* A) k * cj (l k)`. Simplify using `only [vecMul, dotProduct, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Rewrite `this` using `[e, hlA]`. Simplify using `at this`.
-/
theorem psd_map {m : ℕ} (cj : K → K) (σ : K →+* ℂ) (hσ : ∀ z, σ (cj z) = star (σ z)) (hd : DenseRange σ)
    (A : Matrix (Fin m) (Fin m) K) (hH : ∀ i k, A k i = cj (A i k))
    (hP : ∀ l : Fin m → K, l ≠ 0 → 0 < (σ (∑ i, ∑ k, l i * A i k * cj (l k))).re) :
    (A.map σ).PosSemidef ∧ (A.map σ).det ≠ 0 := by
  have hHm : (A.map σ).IsHermitian := by
    ext i k
    simp only [conjTranspose_apply, map_apply]
    rw [hH, hσ, star_star]
  have key : ∀ l : Fin m → K, σ (∑ i, ∑ k, l i * A i k * cj (l k)) =
      star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k))) := by
    intro l
    simp only [map_sum, map_mul, hσ, dotProduct, mulVec, map_apply, Pi.star_apply, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hden : DenseRange (fun l : Fin m → K => fun k => star (σ (l k))) := by
    have h1 : DenseRange (fun z : K => star (σ z)) :=
      (Function.RightInverse.surjective (f := (star : ℂ → ℂ)) (g := star) star_star).denseRange.comp hd
        continuous_star
    exact DenseRange.piMap (f := fun _ : Fin m => fun z : K => star (σ z)) (fun _ => h1)
  have hre : ∀ x : Fin m → ℂ, 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re := by
    intro x
    refine hden.induction_on (p := fun x => 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re) x ?_ ?_
    · apply isClosed_le continuous_const
      simp only [dotProduct, mulVec, Pi.star_apply]
      fun_prop
    · intro l
      show 0 ≤ (star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k)))).re
      by_cases hl : l = 0
      · subst hl
        rw [show (fun k : Fin m => star (σ ((0 : Fin m → K) k))) = 0 by funext k; simp]
        simp
      · rw [← key]; exact (hP l hl).le
  refine ⟨PosSemidef.of_dotProduct_mulVec_nonneg hHm fun x => ?_, ?_⟩
  · rw [Complex.nonneg_iff]
    exact ⟨hre x, (hHm.im_star_dotProduct_mulVec_self x).symm⟩
  · rw [show (A.map σ).det = σ A.det from (RingHom.map_det σ A).symm]
    intro h0
    apply (map_eq_zero_iff σ σ.injective).not.mpr ?_ h0
    intro hdet
    obtain ⟨l, hl, hlA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have := hP l hl
    have e : ∑ i, ∑ k, l i * A i k * cj (l k) = ∑ k, (l ᵥ* A) k * cj (l k) := by
      simp only [vecMul, dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e, hlA] at this
    simp at this

end Dense

end Formalism.L2.Geo.Rec.TraceQuadraticBound

open NumberField NumberField.InfinitePlace

namespace Formalism.L2.Geo.Rec.TraceSumEmbeddings

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

end Formalism.L2.Geo.Rec.TraceSumEmbeddings
