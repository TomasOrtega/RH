import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ZeroOfBlk

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {r : ℕ}

def lastDiag (t : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then t else 0

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality. Simplify using `[lastDiag, Matrix.mulVec, dotProduct]`. Simplify using `[lastDiag, Matrix.mulVec, dotProduct, hi]`.
-/
theorem lastDiag_mulVec (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by
  ext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [lastDiag, Matrix.mulVec, dotProduct]
  · simp [lastDiag, Matrix.mulVec, dotProduct, hi]

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]`. Introduce and unpack `⟨v, hv0, hv⟩`. Apply `hv0` to reduce the goal to its premises. Establish `hZi : Z⁻¹ * Z = 1` using `Matrix.nonsing_inv_mul Z hZ`. Establish `hZhi : (Zᴴ)⁻¹ * Zᴴ = 1` using `Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)`.

Rewrite `hv` using `[Matrix.fromBlocks_mulVec]`. Establish `h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0`. Use function extensionality and compare the values at `fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)`. Establish `h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0`. Use function extensionality and compare the values at `fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)`.

Rewrite `h1`, `h2` using `[lastDiag_mulVec]`. Establish `h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r))`. Rewrite using `[eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r))`. Rewrite using `[eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r))`.

Rewrite using `[← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]`. Establish `hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r))`. Rewrite using `[← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]`. Establish `hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)), (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c`. Introduce `N c i`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))`. Rewrite using `[← Matrix.conjTranspose_nonsing_inv]`. Both sides reduce to the same expression. Establish `hyl` using `congrFun hy (Fin.last r)`.

Establish `hxl` using `congrFun hx (Fin.last r)`. Rewrite `hyl`, `hxl` using `[hsingle]`. Rewrite `hxl` using `[hinv]`. Establish `hprod : (v ∘ Sum.inl) (Fin.last r) * (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)))) = 0`. Take the linear combination `hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl`.

Establish `hx0 : (v ∘ Sum.inl) (Fin.last r) = 0` using `(mul_eq_zero.mp hprod).resolve_right hG`. Establish `hy0 : (v ∘ Sum.inr) (Fin.last r) = 0` using `by rw [hyl, hx0]; ring`. Rewrite `hy` using `[hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero]`. Rewrite `hx` using `[hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero]`. Use function extensionality and compare the values at `s`.

Consider the cases of `s with`. Consider the case `inl i => exact congrFun hx i`. Consider the case `inr i => exact congrFun hy i`.
-/
theorem gram_isUnit (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have hZi : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hZhi : (Zᴴ)⁻¹ * Zᴴ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)
  rw [Matrix.fromBlocks_mulVec] at hv
  have h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)
  have h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)
  rw [lastDiag_mulVec] at h1 h2
  have h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]
    congr 1
    ring
  have h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]
    congr 1
    ring
  have hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]
  have hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)),
      (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c := by
    intro N c i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  have hyl := congrFun hy (Fin.last r)
  have hxl := congrFun hx (Fin.last r)
  rw [hsingle] at hyl hxl
  rw [hinv] at hxl
  have hprod : (v ∘ Sum.inl) (Fin.last r) *
      (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))))
        = 0 := by
    linear_combination hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl
  have hx0 : (v ∘ Sum.inl) (Fin.last r) = 0 := (mul_eq_zero.mp hprod).resolve_right hG
  have hy0 : (v ∘ Sum.inr) (Fin.last r) = 0 := by rw [hyl, hx0]; ring
  rw [hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hy
  rw [hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hx
  funext s
  cases s with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

end Formalism.L2.S.L6.UnitaryStandardVectors
