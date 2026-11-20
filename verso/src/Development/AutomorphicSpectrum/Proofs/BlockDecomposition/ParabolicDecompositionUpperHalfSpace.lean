import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData

open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelPoint

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Unfold `InG JJ at h`. Rewrite `h` using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Take `⟨-, h12, -, h22⟩` from `fromBlocks_inj.mp h`. Simplify using `only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero] at h12 h22`. Conclude with `⟨h12, (neg_add_eq_zero.mp h22).symm⟩`.
-/
theorem block_relations (A B D : Matrix (Fin n) (Fin n) ℂ)
    (h : InG (fromBlocks A B 0 D : M2 n)) : Aᴴ * D = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero] at h12 h22
  exact ⟨h12, (neg_add_eq_zero.mp h22).symm⟩

/- English proof (translation)
Establish `h' : Dᴴ * a = 1`. Establish `h2` using `congrArg conjTranspose h`. Rewrite `h2` using `[conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one]`. Then use the resulting hypothesis. Unfold `InG JJ`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`.

Simplify using `only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, h, h', neg_zero]`.
-/
theorem levi_inG (a D : Matrix (Fin n) (Fin n) ℂ) (h : aᴴ * D = 1) :
    InG (fromBlocks a 0 0 D : M2 n) := by
  have h' : Dᴴ * a = 1 := by
    have h2 := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h2
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, h, h', neg_zero]

/- English proof (translation)
Introduce `n p hp`. Use `set A := (mR p).toBlocks₁₁ with hA`. Use `set B := (mR p).toBlocks₁₂ with hB`. Use `set D := (mR p).toBlocks₂₂ with hD`. Establish `hpm : mR p = fromBlocks A B 0 D`.

Rewrite using `[← hp]`. Conclude with `(fromBlocks_toBlocks (mR p)).symm`. Establish `hG : InG (mR p)` using `p.2`. Rewrite `hG` using `[hpm]`. Take `⟨h1, h2⟩` from `block_relations A B D hG`.

Establish `hDA : D * Aᴴ = 1` using `mul_eq_one_comm.mp h1`. Establish `hADh : A * Dᴴ = 1`. Establish `h3` using `congrArg conjTranspose hDA`. Rewrite `h3` using `[conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one]`. Then use the resulting hypothesis. Establish `hinv : (Aᴴ)⁻¹ = D` using `Matrix.inv_eq_right_inv h1`.

Establish `hDinv : D⁻¹ = Aᴴ` using `Matrix.inv_eq_right_inv hDA`. Use `set b := B * Aᴴ with hb`. Establish `hbh : bᴴ = b`. Rewrite using `[hb, conjTranspose_mul, conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnbG : InG (nU b : M2 n)`. Unfold `InG JJ nU`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, hbh, neg_add_cancel, neg_zero]`. Establish `hdet1 : IsUnit (nU b : M2 n).det`.

Unfold `nU`. Rewrite using `[det_fromBlocks_zero₂₁, det_one, mul_one]`. Conclude with `isUnit_one`. Establish `hmaG : InG (fromBlocks A 0 0 D : M2 n)` using `levi_inG A D h1`. Establish `hM : (fromBlocks A 0 0 D : M2 n) * fromBlocks Dᴴ 0 0 Aᴴ = 1`.

Rewrite using `[fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hADh, hDA, fromBlocks_one]`. Establish `hdet2 : IsUnit (fromBlocks A 0 0 D : M2 n).det` using `Matrix.isUnit_det_of_right_inverse hM`. Use `⟨⟨Matrix.nonsingInvUnit _ hdet1, hnbG⟩, ⟨Matrix.nonsingInvUnit _ hdet2, hmaG⟩, b, A, hbh, Matrix.isUnit_det_of_right_inverse hADh, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (fromBlocks A 0 0 D : M2 n) = fromBlocks A 0 0 (Aᴴ)⁻¹`.

Rewrite using `[hinv]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mR p = nU b * fromBlocks A 0 0 D`. Rewrite using `[hpm]`.

Unfold `nU`. Rewrite using `[fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]`. Rewrite using `[hb, Matrix.mul_assoc, h1, Matrix.mul_one]`. Rewrite using `[hp, Matrix.zero_mul, zero_add, hDinv, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hb, add_comm]`.
-/
theorem siegel_point :
    ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 →
      ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧
        PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧
        p = nb * ma ∧
        ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) *
            ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ =
          b + Complex.I • (a * aᴴ) := by
  intro n p hp
  set A := (mR p).toBlocks₁₁ with hA
  set B := (mR p).toBlocks₁₂ with hB
  set D := (mR p).toBlocks₂₂ with hD
  have hpm : mR p = fromBlocks A B 0 D := by
    rw [← hp]
    exact (fromBlocks_toBlocks (mR p)).symm
  have hG : InG (mR p) := p.2
  rw [hpm] at hG
  obtain ⟨h1, h2⟩ := block_relations A B D hG
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hADh : A * Dᴴ = 1 := by
    have h3 := congrArg conjTranspose hDA
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h3
  have hinv : (Aᴴ)⁻¹ = D := Matrix.inv_eq_right_inv h1
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_right_inv hDA
  set b := B * Aᴴ with hb
  have hbh : bᴴ = b := by
    rw [hb, conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA, Matrix.mul_one]
      _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h2]
      _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = B * Aᴴ := by rw [hADh, Matrix.one_mul]
  have hnbG : InG (nU b : M2 n) := by
    unfold InG JJ nU
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, hbh,
      neg_add_cancel, neg_zero]
  have hdet1 : IsUnit (nU b : M2 n).det := by
    unfold nU
    rw [det_fromBlocks_zero₂₁, det_one, mul_one]
    exact isUnit_one
  have hmaG : InG (fromBlocks A 0 0 D : M2 n) := levi_inG A D h1
  have hM : (fromBlocks A 0 0 D : M2 n) * fromBlocks Dᴴ 0 0 Aᴴ = 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hADh, hDA, fromBlocks_one]
  have hdet2 : IsUnit (fromBlocks A 0 0 D : M2 n).det := Matrix.isUnit_det_of_right_inverse hM
  refine ⟨⟨Matrix.nonsingInvUnit _ hdet1, hnbG⟩, ⟨Matrix.nonsingInvUnit _ hdet2, hmaG⟩, b, A, hbh,
    Matrix.isUnit_det_of_right_inverse hADh, rfl, ?_, ?_, ?_⟩
  · show (fromBlocks A 0 0 D : M2 n) = fromBlocks A 0 0 (Aᴴ)⁻¹
    rw [hinv]
  · apply Subtype.ext
    apply Units.ext
    show mR p = nU b * fromBlocks A 0 0 D
    rw [hpm]
    unfold nU
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
    rw [hb, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [hp, Matrix.zero_mul, zero_add, hDinv, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hb, add_comm]

end GlobalTheory.CompanionTheory.SiegelPoint
