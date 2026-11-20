import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt

noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Dm (X : Fin n → ℝ) (s : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)) 0 0 (diagonal fun j => ((Real.exp (-(s * X j)) : ℝ) : ℂ))

/- English proof (translation)
Simplify using `only [Dm, fromBlocks_multiply, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Rewrite using `[← Complex.ofReal_mul, ← Real.exp_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `j`. Rewrite using `[← Complex.ofReal_mul, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dm_mul (X : Fin n → ℝ) (s t : ℝ) : Dm X s * Dm X t = Dm X (s + t) := by
  simp only [Dm, fromBlocks_multiply, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 2
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

/- English proof (translation)
Simplify using `[Dm, fromBlocks_one]`.
-/
theorem Dm_zero (X : Fin n → ℝ) : Dm X 0 = 1 := by
  simp [Dm, fromBlocks_one]

def dGL (X : Fin n → ℝ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨Dm X s, Dm X (-s), by rw [Dm_mul, add_neg_cancel, Dm_zero], by rw [Dm_mul, neg_add_cancel, Dm_zero]⟩

/- English proof (translation)
Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `[Complex.conj_ofReal]`.
-/
theorem diag_conjT_mul (f g : Fin n → ℝ) :
    (diagonal fun j => ((f j : ℝ) : ℂ))ᴴ * diagonal (fun j => ((g j : ℝ) : ℂ)) = diagonal fun j => ((f j * g j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext j
  simp [Complex.conj_ofReal]

/- English proof (translation)
Establish `h' : Bᴴ * A = 1`. Use `congrArg Matrix.conjTranspose h` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul]`. Unfold `InG JJ`. Rewrite using `[fromBlocks_conjTranspose]`.

Simplify using `only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero]`. Rewrite using `[h, h']`.
-/
theorem inG_blocks (A B : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * B = 1) : InG (fromBlocks A 0 0 B) := by
  have h' : Bᴴ * A = 1 := by
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul] using this
  unfold InG JJ
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [h, h']

/- English proof (translation)
Apply `inG_blocks` to reduce the goal to its premises. Rewrite using `[diag_conjT_mul, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[← Real.exp_add]`.

Simplify using the standard rewrite rules.
-/
theorem inG_Dm (X : Fin n → ℝ) (s : ℝ) : InG (Dm X s) := by
  apply inG_blocks
  rw [diag_conjT_mul, ← diagonal_one]
  congr 1
  funext j
  rw [← Real.exp_add]
  simp

def aD (X : Fin n → ℝ) (s : ℝ) : GR n := ⟨dGL X s, inG_Dm X s⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem isDil_aD (X : Fin n → ℝ) (s : ℝ) : IsDil X s (aD X s) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `h.trans h'.symm`.
-/
theorem isDil_unique (X : Fin n → ℝ) (s : ℝ) (a a' : GR n) (h : IsDil X s a) (h' : IsDil X s a') : a = a' := by
  apply Subtype.ext
  apply Units.ext
  exact h.trans h'.symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Unfold `InG at hg`. Rewrite using `[hg]`.
-/
theorem form_inv (g : M2 n) (hg : InG g) (V : Fin n ⊕ Fin n → ℂ) :
    star (g *ᵥ V) ⬝ᵥ (JJ n *ᵥ (g *ᵥ V)) = star V ⬝ᵥ (JJ n *ᵥ V) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold InG at hg
  rw [hg]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> simp [JJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]`.
-/
theorem JJ_mulVec (y z : Fin n → ℂ) : JJ n *ᵥ Sum.elim y z = Sum.elim z (-y) := by
  funext i
  rcases i with i | i <;> simp [JJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

/- English proof (translation)
Simplify using `[dotProduct, Fintype.sum_sum_type]`.
-/
theorem dot_elim (a b c d : Fin n → ℂ) : Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> rfl`.
-/
theorem star_elim (a b : Fin n → ℂ) : star (Sum.elim a b) = Sum.elim (star a) (star b) := by
  funext i
  rcases i with i | i <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]`.
-/
theorem mulVec_elim (g : M2 n) (y z : Fin n → ℂ) :
    g *ᵥ Sum.elim y z = Sum.elim (g.toBlocks₁₁ *ᵥ y + g.toBlocks₁₂ *ᵥ z) (g.toBlocks₂₁ *ᵥ y + g.toBlocks₂₂ *ᵥ z) := by
  funext i
  rcases i with i | i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
    toBlocks₂₂]

/- English proof (translation)
Introduce `h0`. Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `key` using `form_inv g hg (Sum.elim (w • x) x)`. Rewrite `key` using `[mulVec_elim]`. Establish `hl : g.toBlocks₂₁ *ᵥ (w • x) + g.toBlocks₂₂ *ᵥ x = 0`.

Rewrite using `[Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.add_mulVec]`. Conclude with `hx`. Rewrite `key` using `[hl, JJ_mulVec, JJ_mulVec, star_elim, star_elim, dot_elim, dot_elim]`. Establish `hs : star (w • x) = star w • star x`. Use function extensionality and compare the values at `j`.

Simplify using `[mul_comm]`. Rewrite `key` using `[hs]`. Simplify using `only [dotProduct_zero, zero_add, Pi.star_apply, star_zero, zero_dotProduct, dotProduct_neg, smul_dotProduct, dotProduct_smul, smul_eq_mul] at key`. Establish `hxx : star x ⬝ᵥ x ≠ 0` using `fun h => hx0 (dotProduct_star_self_eq_zero.mp h)`. Break down `hw with rfl | rfl` into its components or cases.

Apply `hxx` to reduce the goal to its premises. Establish `h2 : star Complex.I = -Complex.I` using `by simp [Complex.star_def]`. Rewrite `key` using `[h2]`. Establish `: (-(2 * Complex.I)) * (star x ⬝ᵥ x) = 0` using `by linear_combination -key`. Break down `mul_eq_zero.mp this with h | h` into its components or cases.

Simplify using `at h`. Conclude with `h`. Apply `hxx` to reduce the goal to its premises. Establish `h2 : star (-Complex.I) = Complex.I` using `by simp [Complex.star_def]`. Rewrite `key` using `[h2]`.

Establish `: (2 * Complex.I) * (star x ⬝ᵥ x) = 0` using `by linear_combination -key`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Simplify using `at h`. Conclude with `h`.
-/
theorem u_det_ne (g : M2 n) (hg : InG g) (w : ℂ) (hw : w = Complex.I ∨ w = -Complex.I) :
    (w • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have key := form_inv g hg (Sum.elim (w • x) x)
  rw [mulVec_elim] at key
  have hl : g.toBlocks₂₁ *ᵥ (w • x) + g.toBlocks₂₂ *ᵥ x = 0 := by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.add_mulVec]
    exact hx
  rw [hl, JJ_mulVec, JJ_mulVec, star_elim, star_elim, dot_elim, dot_elim] at key
  have hs : star (w • x) = star w • star x := by
    funext j; simp [mul_comm]
  rw [hs] at key
  simp only [dotProduct_zero, zero_add, Pi.star_apply, star_zero, zero_dotProduct, dotProduct_neg, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at key
  have hxx : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.mp h)
  rcases hw with rfl | rfl
  · apply hxx
    have h2 : star Complex.I = -Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (-(2 * Complex.I)) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h
  · apply hxx
    have h2 : star (-Complex.I) = Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (2 * Complex.I) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h

/- English proof (translation)
The claim follows from `u_det_ne _ h.2 _ (Or.inl rfl)`.
-/
theorem automorphy_first_det_ne_zero (h : GR n) : (u1 (mR h)).det ≠ 0 := u_det_ne _ h.2 _ (Or.inl rfl)

/- English proof (translation)
Establish `: u2 (mR h) = (-Complex.I) • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂`. Simplify using `[u2, neg_smul]`. Rewrite using `[this]`. Conclude with `u_det_ne _ h.2 _ (Or.inr rfl)`.
-/
theorem automorphy_second_det_ne_zero (h : GR n) : (u2 (mR h)).det ≠ 0 := by
  have : u2 (mR h) = (-Complex.I) • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ := by
    simp [u2, neg_smul]
  rw [this]
  exact u_det_ne _ h.2 _ (Or.inr rfl)

/- English proof (translation)
Use `(Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h.1)` as an intermediate fact. Conclude with `this.ne_zero`.
-/
theorem det_mR_ne (h : GR n) : (mR h).det ≠ 0 := by
  have := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h.1)
  exact this.ne_zero

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mR : Continuous (mR (n := n)) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))`.
-/
theorem continuous_group_lower_left_block : Continuous fun h : GR n => (mR h).toBlocks₂₁ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))

/- English proof (translation)
The claim follows from `continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))`.
-/
theorem continuous_group_lower_right_block : Continuous fun h : GR n => (mR h).toBlocks₂₂ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))

/- English proof (translation)
Establish `c1 : Continuous fun h : GR n => (mR h).det` using `continuous_mR.matrix_det`. Establish `c2 : Continuous fun h : GR n => (u1 (mR h)).det`. Establish `: Continuous fun h : GR n => Complex.I • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂` using `(continuous_group_lower_left_block.const_smul Complex.I).add continuous_group_lower_right_block`. Unfold `u1`. Conclude with `this.matrix_det`.

Establish `c3 : Continuous fun h : GR n => (u2 (mR h)).det`. Establish `: Continuous fun h : GR n => -(Complex.I • (mR h).toBlocks₂₁) + (mR h).toBlocks₂₂` using `(continuous_group_lower_left_block.const_smul Complex.I).neg.add continuous_group_lower_right_block`. Unfold `u2`. Conclude with `this.matrix_det`. Use `⟨?_, fun k => ?_⟩` and prove the remaining obligations.

Unfold `F0 f0`. Conclude with `(c1.zpow₀ e fun h => Or.inl (det_mR_ne h)).mul ((c2.zpow₀ _ fun h => Or.inl (automorphy_first_det_ne_zero h)).mul (c3.zpow₀ _ fun h => Or.inl (automorphy_second_det_ne_zero h)))`. Unfold `F0 f0`. Conclude with `mul_ne_zero (zpow_ne_zero _ (det_mR_ne k)) (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero k)) (zpow_ne_zero _ (automorphy_second_det_ne_zero k)))`.
-/
theorem spherical_section_continuous_ne_zero (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, F0 p q e k ≠ 0 := by
  have c1 : Continuous fun h : GR n => (mR h).det := continuous_mR.matrix_det
  have c2 : Continuous fun h : GR n => (u1 (mR h)).det := by
    have : Continuous fun h : GR n => Complex.I • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).add continuous_group_lower_right_block
    unfold u1
    exact this.matrix_det
  have c3 : Continuous fun h : GR n => (u2 (mR h)).det := by
    have : Continuous fun h : GR n => -(Complex.I • (mR h).toBlocks₂₁) + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).neg.add continuous_group_lower_right_block
    unfold u2
    exact this.matrix_det
  refine ⟨?_, fun k => ?_⟩
  · unfold F0 f0
    exact (c1.zpow₀ e fun h => Or.inl (det_mR_ne h)).mul
      ((c2.zpow₀ _ fun h => Or.inl (automorphy_first_det_ne_zero h)).mul (c3.zpow₀ _ fun h => Or.inl (automorphy_second_det_ne_zero h)))
  · unfold F0 f0
    exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne k))
      (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero k)) (zpow_ne_zero _ (automorphy_second_det_ne_zero k)))

end PositivityTheory.Rg.Sw.AbsSt
