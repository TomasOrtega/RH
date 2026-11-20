import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `set v : n → ℂ := ⇑(hM.eigenvectorBasis i) with hv`. Establish `hv0 : v ≠ 0`. Introduce `h0`. Establish `h1` using `hM.eigenvectorBasis.orthonormal.ne_zero i`. Apply `h1` to reduce the goal to its premises.

Use extensionality with `j`. Simplify `congrFun h0 j` using `[hv]`. Establish `hMv : M *ᵥ v = (hM.eigenvalues i : ℂ) • v` using `hM.mulVec_eigenvectorBasis i`. Establish `h0` using `h.dotProduct_mulVec_nonneg v`. Rewrite `h0` using `[add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hMv, smul_smul, ← add_smul, dotProduct_smul, smul_eq_mul]`.

Establish `hs : 0 < star v ⬝ᵥ v` using `dotProduct_star_self_pos_iff.mpr hv0`. Establish `hx : ((a : ℂ) + (b : ℂ) * (hM.eigenvalues i : ℂ)) = ((a + b * hM.eigenvalues i : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `h0` using `[hx]`. Establish `h2` using `(Complex.nonneg_iff.mp h0).1`. Rewrite `h2` using `[Complex.re_ofReal_mul]`.

Conclude with `(mul_nonneg_iff_of_pos_right (Complex.pos_iff.mp hs).1).mp h2`.
-/
theorem add_mul_eigenvalue_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian) {a b : ℝ}
    (h : ((a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • M).PosSemidef) (i : n) :
    0 ≤ a + b * hM.eigenvalues i := by
  set v : n → ℂ := ⇑(hM.eigenvectorBasis i) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := hM.eigenvectorBasis.orthonormal.ne_zero i
    apply h1
    ext j
    simpa [hv] using congrFun h0 j
  have hMv : M *ᵥ v = (hM.eigenvalues i : ℂ) • v := hM.mulVec_eigenvectorBasis i
  have h0 := h.dotProduct_mulVec_nonneg v
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hMv, smul_smul, ← add_smul,
    dotProduct_smul, smul_eq_mul] at h0
  have hs : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv0
  have hx : ((a : ℂ) + (b : ℂ) * (hM.eigenvalues i : ℂ)) = ((a + b * hM.eigenvalues i : ℝ) : ℂ) := by
    push_cast; ring
  rw [hx] at h0
  have h2 := (Complex.nonneg_iff.mp h0).1
  rw [Complex.re_ofReal_mul] at h2
  exact (mul_nonneg_iff_of_pos_right (Complex.pos_iff.mp hs).1).mp h2

/- English proof (translation)
Establish `hA : A.PosSemidef`. Establish `e : A = ((1 / (2 * c) : ℝ) : ℂ) • (((c : ℂ) • A + H) + ((c : ℂ) • A - H))`. Rewrite using `[show ((c : ℂ) • A + H) + ((c : ℂ) • A - H) = ((2 * c : ℝ) : ℂ) • A by push_cast; rw [mul_smul, two_smul]; abel, smul_smul, ← Complex.ofReal_mul, one_div_mul_cancel (by positivity), Complex.ofReal_one, one_smul]`. Rewrite using `[e]`. Conclude with `(h₂.add h₁).smul (Complex.zero_le_real.mpr (by positivity))`.

Take `⟨hre, him⟩` from `Complex.nonneg_iff.mp hA.det_nonneg`. Use `⟨hre, him.symm, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : A.det = 0`. Take `⟨v, hv0, hAv⟩` from `exists_mulVec_eq_zero_iff.mpr h0`. Establish `e1 : star v ⬝ᵥ (((c : ℂ) • A - H) *ᵥ v) = -(star v ⬝ᵥ (H *ᵥ v))`.

Rewrite using `[sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, dotProduct_neg]`. Establish `e2 : star v ⬝ᵥ (((c : ℂ) • A + H) *ᵥ v) = star v ⬝ᵥ (H *ᵥ v)`. Rewrite using `[add_mulVec, smul_mulVec, hAv, smul_zero, zero_add]`. Establish `p1` using `h₁.dotProduct_mulVec_nonneg v`. Establish `p2` using `h₂.dotProduct_mulVec_nonneg v`.

Rewrite `p1` using `[e1]`. Rewrite `p2` using `[e2]`. Establish `hz : star v ⬝ᵥ (H *ᵥ v) = 0` using `le_antisymm (neg_nonneg.mp p1) p2`. Establish `hw` using `(h₁.dotProduct_mulVec_zero_iff v).mp (by rw [e1, hz, neg_zero])`. Rewrite `hw` using `[sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, neg_eq_zero]`.

Rewrite using `[exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hw⟩, norm_zero]`. Conclude with `mul_nonneg (pow_nonneg hc.le _) hre`. Take `⟨L, hL⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg`. Rewrite `hL` using `[star_eq_conjTranspose]`. Establish `hLu : IsUnit L.det` using `isUnit_iff_ne_zero.mpr fun hl => h0 (by rw [hL, det_mul, hl, mul_zero])`.

Establish `hLHu : IsUnit Lᴴ.det`. Rewrite using `[det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hLu))`. Use `set M := (L⁻¹)ᴴ * H * L⁻¹ with hMdef`. Establish `hHM : H = Lᴴ * M * L`.

Rewrite using `[hMdef, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.mul_one]`. Establish `hA1 : (L⁻¹)ᴴ * A * L⁻¹ = 1`. Rewrite using `[hL, conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Lᴴ)⁻¹ Lᴴ L, Matrix.nonsing_inv_mul _ hLHu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hLu]`. Establish `hconj : ∀ s : ℝ, (L⁻¹)ᴴ * ((c : ℂ) • A + (s : ℂ) • H) * L⁻¹ = (c : ℂ) • 1 + (s : ℂ) • M`. Introduce `s`.

Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hA1, hMdef]`. Establish `hP : ∀ s : ℝ, s = 1 ∨ s = -1 → ((c : ℂ) • (1 : Matrix n n ℂ) + (s : ℂ) • M).PosSemidef`. Introduce and unpack `s (rfl | rfl)`. Rewrite using `[← hconj]`. Simplify using `using h₂.conjTranspose_mul_mul_same L⁻¹`.

Rewrite using `[← hconj]`. Establish `e : (c : ℂ) • A + ((-1 : ℝ) : ℂ) • H = (c : ℂ) • A - H` using `by push_cast; rw [neg_one_smul, ← sub_eq_add_neg]`. Rewrite using `[e]`. Conclude with `h₁.conjTranspose_mul_mul_same L⁻¹`. Establish `hM : M.IsHermitian`.

Establish `h3` using `(hP 1 (Or.inl rfl)).isHermitian`. Rewrite `h3` using `[IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_one, map_one, one_smul] at h3`. Conclude with `add_left_cancel h3`. Establish `hb : ∀ i, |hM.eigenvalues i| ≤ c` using `fun i => by`.

Establish `u` using `add_mul_eigenvalue_nonneg hM (hP 1 (Or.inl rfl)) i`. Establish `l` using `add_mul_eigenvalue_nonneg hM (hP (-1) (Or.inr rfl)) i`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hdA : A.det = Lᴴ.det * L.det` using `by rw [hL, det_mul]`.

Establish `hnA : ‖A.det‖ = A.det.re`. Rewrite using `[← Complex.re_add_im A.det, ← him]`. Simplify using `[Complex.norm_real, abs_of_nonneg hre]`. Establish `hdH : ‖H.det‖ = ‖M.det‖ * ‖A.det‖`. Rewrite using `[hHM, det_mul, det_mul, hdA]`.

Simplify using `only [norm_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdM : ‖M.det‖ ≤ c ^ Fintype.card n`. Rewrite using `[hM.det_eq_prod_eigenvalues, norm_prod]`. Use `(Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_).trans_eq (by rw [Finset.prod_const, Finset.card_univ] : ∏ _i : n, c = c ^ Fintype.card n)` and prove the remaining obligations.

Use `hb i` as an intermediate fact. Rewrite using `[RCLike.norm_ofReal]` and apply the resulting hypothesis. Rewrite using `[hdH, ← hnA]`. Conclude with `mul_le_mul_of_nonneg_right hdM (norm_nonneg _)`.
-/
theorem norm_det_le_of_loewner {H A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : ((c : ℂ) • A - H).PosSemidef) (h₂ : ((c : ℂ) • A + H).PosSemidef) :
    0 ≤ A.det.re ∧ A.det.im = 0 ∧ ‖H.det‖ ≤ c ^ Fintype.card n * A.det.re := by
  have hA : A.PosSemidef := by
    have e : A = ((1 / (2 * c) : ℝ) : ℂ) • (((c : ℂ) • A + H) + ((c : ℂ) • A - H)) := by
      rw [show ((c : ℂ) • A + H) + ((c : ℂ) • A - H) = ((2 * c : ℝ) : ℂ) • A by
        push_cast; rw [mul_smul, two_smul]; abel, smul_smul, ← Complex.ofReal_mul,
        one_div_mul_cancel (by positivity), Complex.ofReal_one, one_smul]
    rw [e]
    exact (h₂.add h₁).smul (Complex.zero_le_real.mpr (by positivity))
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hA.det_nonneg
  refine ⟨hre, him.symm, ?_⟩
  by_cases h0 : A.det = 0
  · obtain ⟨v, hv0, hAv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have e1 : star v ⬝ᵥ (((c : ℂ) • A - H) *ᵥ v) = -(star v ⬝ᵥ (H *ᵥ v)) := by
      rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, dotProduct_neg]
    have e2 : star v ⬝ᵥ (((c : ℂ) • A + H) *ᵥ v) = star v ⬝ᵥ (H *ᵥ v) := by
      rw [add_mulVec, smul_mulVec, hAv, smul_zero, zero_add]
    have p1 := h₁.dotProduct_mulVec_nonneg v
    have p2 := h₂.dotProduct_mulVec_nonneg v
    rw [e1] at p1
    rw [e2] at p2
    have hz : star v ⬝ᵥ (H *ᵥ v) = 0 := le_antisymm (neg_nonneg.mp p1) p2
    have hw := (h₁.dotProduct_mulVec_zero_iff v).mp (by rw [e1, hz, neg_zero])
    rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, neg_eq_zero] at hw
    rw [exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hw⟩, norm_zero]
    exact mul_nonneg (pow_nonneg hc.le _) hre
  · obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    rw [star_eq_conjTranspose] at hL
    have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr fun hl => h0 (by rw [hL, det_mul, hl, mul_zero])
    have hLHu : IsUnit Lᴴ.det := by
      rw [det_conjTranspose]
      exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hLu))
    set M := (L⁻¹)ᴴ * H * L⁻¹ with hMdef
    have hHM : H = Lᴴ * M * L := by
      rw [hMdef, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu,
        Matrix.mul_one]
    have hA1 : (L⁻¹)ᴴ * A * L⁻¹ = 1 := by
      rw [hL, conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Lᴴ)⁻¹ Lᴴ L,
        Matrix.nonsing_inv_mul _ hLHu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hLu]
    have hconj : ∀ s : ℝ, (L⁻¹)ᴴ * ((c : ℂ) • A + (s : ℂ) • H) * L⁻¹ = (c : ℂ) • 1 + (s : ℂ) • M := by
      intro s
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        hA1, hMdef]
    have hP : ∀ s : ℝ, s = 1 ∨ s = -1 → ((c : ℂ) • (1 : Matrix n n ℂ) + (s : ℂ) • M).PosSemidef := by
      rintro s (rfl | rfl)
      · rw [← hconj]
        simpa using h₂.conjTranspose_mul_mul_same L⁻¹
      · rw [← hconj]
        have e : (c : ℂ) • A + ((-1 : ℝ) : ℂ) • H = (c : ℂ) • A - H := by
          push_cast; rw [neg_one_smul, ← sub_eq_add_neg]
        rw [e]
        exact h₁.conjTranspose_mul_mul_same L⁻¹
    have hM : M.IsHermitian := by
      have h3 := (hP 1 (Or.inl rfl)).isHermitian
      rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one] at h3
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_one, map_one, one_smul] at h3
      exact add_left_cancel h3
    have hb : ∀ i, |hM.eigenvalues i| ≤ c := fun i => by
      have u := add_mul_eigenvalue_nonneg hM (hP 1 (Or.inl rfl)) i
      have l := add_mul_eigenvalue_nonneg hM (hP (-1) (Or.inr rfl)) i
      rw [abs_le]
      constructor <;> linarith
    have hdA : A.det = Lᴴ.det * L.det := by rw [hL, det_mul]
    have hnA : ‖A.det‖ = A.det.re := by
      rw [← Complex.re_add_im A.det, ← him]
      simp [Complex.norm_real, abs_of_nonneg hre]
    have hdH : ‖H.det‖ = ‖M.det‖ * ‖A.det‖ := by
      rw [hHM, det_mul, det_mul, hdA]
      simp only [norm_mul]
      ring
    have hdM : ‖M.det‖ ≤ c ^ Fintype.card n := by
      rw [hM.det_eq_prod_eigenvalues, norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_).trans_eq
        (by rw [Finset.prod_const, Finset.card_univ] : ∏ _i : n, c = c ^ Fintype.card n)
      have := hb i
      rwa [RCLike.norm_ofReal]
    rw [hdH, ← hnA]
    exact mul_le_mul_of_nonneg_right hdM (norm_nonneg _)

end GroundTheory.Heights₂.Heights.LowerBoundFree
