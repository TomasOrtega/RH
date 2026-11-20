import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.LocOpA

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[← fromBlocks_one, fromBlocks_neg]`. Simplify using `[JJ, fromBlocks_multiply]`.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← fromBlocks_one, fromBlocks_neg]
  simp [JJ, fromBlocks_multiply]

/- English proof (translation)
Establish `h'` using `h`. Unfold `InG at h'`. Rewrite `h'` using `[← fromBlocks_toBlocks g]`. Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h'`. Take `⟨h1, h2, h3, h4⟩` from `Matrix.fromBlocks_inj.1 h'`.

Conclude with `⟨h1, h2, h3, h4⟩`.
-/
theorem inG_blocks {g : M2 n} (h : InG g) :
    -(g.toBlocks₂₁ᴴ * g.toBlocks₁₁) + g.toBlocks₁₁ᴴ * g.toBlocks₂₁ = 0 ∧
    -(g.toBlocks₂₁ᴴ * g.toBlocks₁₂) + g.toBlocks₁₁ᴴ * g.toBlocks₂₂ = 1 ∧
    -(g.toBlocks₂₂ᴴ * g.toBlocks₁₁) + g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = -1 ∧
    -(g.toBlocks₂₂ᴴ * g.toBlocks₁₂) + g.toBlocks₁₂ᴴ * g.toBlocks₂₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g] at h'
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, Matrix.neg_mul] at h'
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h'
  exact ⟨h1, h2, h3, h4⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `inG_blocks h`. Use `set A := g.toBlocks₁₁`. Use `set B := g.toBlocks₁₂`. Use `set C := g.toBlocks₂₁`. Use `set D := g.toBlocks₂₂`.

Establish `e1 : Aᴴ * C = Cᴴ * A` using `by rw [← sub_eq_zero, sub_eq_neg_add]; exact h1`. Establish `e2 : Aᴴ * D = 1 + Cᴴ * B` using `by rw [← h2]; abel`. Establish `e3 : Bᴴ * C = -1 + Dᴴ * A` using `by rw [← h3]; abel`. Establish `e4 : Bᴴ * D = Dᴴ * B` using `by rw [← sub_eq_zero, sub_eq_neg_add]; exact h4`. Simplify using `only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul]`.

Rewrite using `[e1, e2, e3, e4, hs]`. Use `module`.
-/
theorem key_identity {g : M2 n} (h : InG g) (s : ℂ) (hs : star s = -s) :
    (s • g.toBlocks₁₁ + g.toBlocks₁₂)ᴴ * (s • g.toBlocks₂₁ + g.toBlocks₂₂) -
      (s • g.toBlocks₂₁ + g.toBlocks₂₂)ᴴ * (s • g.toBlocks₁₁ + g.toBlocks₁₂) = (-(2 * s)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := inG_blocks h
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set C := g.toBlocks₂₁
  set D := g.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := by rw [← sub_eq_zero, sub_eq_neg_add]; exact h1
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := by rw [← sub_eq_zero, sub_eq_neg_add]; exact h4
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [e1, e2, e3, e4, hs]
  module

/- English proof (translation)
Introduce `h0`. Take `⟨x, hx0, hx⟩` from `(Matrix.exists_mulVec_eq_zero_iff).2 h0`. Establish `e : star x ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ x) = 0`. Rewrite using `[Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_zero, dotProduct_mulVec, ← Matrix.star_mulVec, hx, star_zero, zero_dotProduct, sub_zero]`. Rewrite `e` using `[hk]`.

Simplify using `only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at e`. Break down `e with e | e` into its components or cases. Conclude with `hc e`. Conclude with `hx0 (dotProduct_star_self_eq_zero.1 e)`.
-/
theorem det_ne_zero_of_key {P Q : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : c ≠ 0) (hk : Pᴴ * Q - Qᴴ * P = c • 1) :
    Q.det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have e : star x ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ x) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
      dotProduct_zero, dotProduct_mulVec, ← Matrix.star_mulVec, hx, star_zero, zero_dotProduct, sub_zero]
  rw [hk] at e
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at e
  rcases e with e | e
  · exact hc e
  · exact hx0 (dotProduct_star_self_eq_zero.1 e)

/- English proof (translation)
Establish `hk` using `key_identity h Complex.I (by simp)`. Use `det_ne_zero_of_key (c := -(2 * Complex.I)) (P := Complex.I • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_` and prove the remaining obligations. Unfold `u1`. Conclude with `hk`.
-/
theorem det_first_block_ne_zero_group {g : M2 n} (h : InG g) : (u1 g).det ≠ 0 := by
  have hk := key_identity h Complex.I (by simp)
  refine det_ne_zero_of_key (c := -(2 * Complex.I)) (P := Complex.I • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_
  unfold u1
  exact hk

/- English proof (translation)
Establish `hk` using `key_identity h (-Complex.I) (by simp)`. Use `det_ne_zero_of_key (c := -(2 * -Complex.I)) (P := (-Complex.I) • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_` and prove the remaining obligations. Unfold `u2`. Rewrite using `[← neg_smul]`. Conclude with `hk`.
-/
theorem det_second_cayley_block_ne {g : M2 n} (h : InG g) : (u2 g).det ≠ 0 := by
  have hk := key_identity h (-Complex.I) (by simp)
  refine det_ne_zero_of_key (c := -(2 * -Complex.I)) (P := (-Complex.I) • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_
  unfold u2
  rw [← neg_smul]
  exact hk

def linv (M : M2 n) : M2 n := -(JJ n * Mᴴ * JJ n)

/- English proof (translation)
Unfold `linv InG at *`. Rewrite using `[Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, JJ_mul_JJ, neg_neg]`.
-/
theorem linv_mul {M : M2 n} (h : InG M) : linv M * M = 1 := by
  unfold linv InG at *
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, JJ_mul_JJ, neg_neg]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (linv_mul h)`.
-/
theorem mul_linv {M : M2 n} (h : InG M) : M * linv M = 1 := mul_eq_one_comm.1 (linv_mul h)

def mkG (M : M2 n) (h : InG M) : GR n := ⟨⟨M, linv M, mul_linv h, linv_mul h⟩, h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mR_mkG (M : M2 n) (h : InG M) : mR (mkG M h) = M := rfl

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem inG_of (g : GR n) : InG (mR g) := g.2

/- English proof (translation)
Unfold `mR`. Use `fun_prop`.
-/
theorem continuous_mR : Continuous (fun g : GR n => mR g) := by unfold mR; fun_prop

/- English proof (translation)
Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `hf`. Express the relevant statement in the definitionally equal form `Continuous fun x => linv (f x)`. Unfold `linv`. Use `fun_prop`.
-/
theorem continuous_mkG {X : Type} [TopologicalSpace X] {f : X → M2 n} (hf : Continuous f) (h : ∀ x, InG (f x)) :
    Continuous (fun x => mkG (f x) (h x)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact hf
  change Continuous fun x => linv (f x)
  unfold linv
  fun_prop

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Complex.ext ?_ ?_ <;> (simp [herm, conjTranspose_apply]; try ring)`.
-/
theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x).IsHermitian := by
  ext i j
  refine Complex.ext ?_ ?_ <;> (simp [herm, conjTranspose_apply]; try ring)

/- English proof (translation)
Unfold `InG nU JJ`. Simplify using `only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one, conjTranspose_zero, hb.eq]`. Simplify using the standard rewrite rules.
-/
theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG nU JJ
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one, conjTranspose_zero, hb.eq]
  simp

/- English proof (translation)
Unfold `herm`. Use `fun_prop`.
-/
theorem continuous_herm : Continuous (herm (n := n)) := by
  unfold herm
  fun_prop

def nbEl (x : Fin n → Fin n → ℝ) : GR n := mkG (nU (herm x)) (inG_nU (herm_isHermitian x))

/- English proof (translation)
Unfold `nbEl`. Use `continuous_mkG ?_ _` and prove the remaining obligations. Unfold `nU`. Conclude with `Continuous.matrix_fromBlocks continuous_const continuous_herm continuous_const continuous_const`.
-/
theorem continuous_nbEl : Continuous (nbEl (n := n)) := by
  unfold nbEl
  refine continuous_mkG ?_ _
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_herm continuous_const continuous_const

end PositivityTheory.Rg.Sw.AbsSt.LocOpA
