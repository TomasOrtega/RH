import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x6

open C2x5

variable {k r : ℕ}

/- English proof (translation)
Rewrite using `[ggBlockA k r z hz a b, hzz_real]`. Simplify using `only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]`. Apply the tactic sequence `by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r`. Substitute `ha hb` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]`. Simplify using `[ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[ha]`.

Simplify using `[ha, hab]`.
-/
lemma herm_ff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by
  rw [ggBlockA k r z hz a b, hzz_real]
  simp only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha hb; simp
  · simp [ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]
  · simp [ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]
  · by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [ha, hab]

/- English proof (translation)
Rewrite using `[dotProduct]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.
-/
lemma E_cast {n : ℕ} (x : Fin n → ℂ) : star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]`.
-/
lemma E_unit {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  rw [← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]

/- English proof (translation)
Establish `h1 : ‖star b ⬝ᵥ a‖ ≤ ∑ i, ‖b i‖ * ‖a i‖`. Rewrite using `[dotProduct]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Pi.star_apply, norm_star]`.

Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b i‖) (fun i => ‖a i‖)`. Simplify using `only [Complex.normSq_eq_norm_sq]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma euclid_cs {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (star b ⬝ᵥ a) ≤ (∑ i, Complex.normSq (a i)) * (∑ i, Complex.normSq (b i)) := by
  have h1 : ‖star b ⬝ᵥ a‖ ≤ ∑ i, ‖b i‖ * ‖a i‖ := by
    rw [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b i‖) (fun i => ‖a i‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖star b ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖b i‖ * ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖a i‖ ^ 2) := h2
    _ = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := mul_comm _ _

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `[GBasic.Hpk_eq]`.
-/
lemma Hpk_mul_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
  rw [Matrix.mul_apply]
  simp [GBasic.Hpk_eq]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r j)]`. Rewrite using `[GBasic.Hpk_eq, if_pos (GBasic.sig_sig k r j).symm, GBasic.sgn_sig]`. Introduce `l _ hl`. Rewrite using `[GBasic.Hpk_eq, if_neg, mul_zero]`. Introduce `h`.

Conclude with `hl (by rw [h, GBasic.sig_sig])`. Simplify using the standard rewrite rules.
-/
lemma mul_Hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (M * Hpk k r) i j = M i (GBasic.sig k r j) * GBasic.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r j)]
  · rw [GBasic.Hpk_eq, if_pos (GBasic.sig_sig k r j).symm, GBasic.sgn_sig]
  · intro l _ hl
    rw [GBasic.Hpk_eq, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, GBasic.sig_sig])
  · simp

/- English proof (translation)
Unfold `GBasic.sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma normSq_sgn (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by
  unfold GBasic.sgn
  split_ifs <;> simp

end C2x6

open C2x5 C2x6

/- English proof (translation)
Introduce `k r z z' hz hz' g hg`. Establish `hH` using `GBasic.Hpk_herm k r`. Establish `hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w`. Introduce `v w`. Simplify using `only [herm]`.

Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with a | a <;> rcases j with b | b`. Simplify using `only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]`. Conclude with `herm_ff hz.1 a b`.

Simplify using `only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]`. Both sides reduce to the same expression. Simplify using `only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]`. Rewrite using `[ggHerm_swap _ hH]`. Both sides reduce to the same expression.

Simplify using `only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]`. Rewrite using `[hpres]`. Conclude with `herm_ff hz'.1 a b`.
-/
theorem gram_block_form : C2.GramBlocks := by
  intro k r z z' hz hz' g hg
  have hH := GBasic.Hpk_herm k r

  have hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    simp only [herm]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    exact herm_ff hz.1 a b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [ggHerm_swap _ hH]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [hpres]
    exact herm_ff hz'.1 a b

/- English proof (translation)
Introduce `k r`. Establish `hH` using `GBasic.Hpk_herm k r`. Establish `hsq` using `GBasic.Hpk_sq k r`. Use `⟨?_, hsq, fun v => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r`.

Rewrite using `[hH, hsq, Matrix.one_mul]`. Simplify using `only [herm]`. Rewrite using `[E_cast, E_unit _ hH hsq]`. Establish `hcs` using `euclid_cs (Hpk k r *ᵥ v) v`. Rewrite `hcs` using `[E_unit _ hH hsq]`.

Use `set S := ∑ i, Complex.normSq (v i)`. Establish `hS : 0 ≤ S` using `Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _`. Establish `h1 : ‖herm (Hpk k r) v v‖ ^ 2 ≤ S ^ 2`. Rewrite using `[← Complex.normSq_eq_norm_sq, sq]`. Conclude with `hcs`.

Establish `h2 : ‖herm (Hpk k r) v v‖ ≤ S` using `(pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp h1`. Conclude with `(Complex.re_le_norm _).trans h2`.
-/
theorem majorant_estimate : C2.Majorant := by
  intro k r
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  refine ⟨?_, hsq, fun v => ⟨?_, ?_⟩⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hH, hsq, Matrix.one_mul]
  · simp only [herm]
    rw [E_cast, E_unit _ hH hsq]
  · have hcs := euclid_cs (Hpk k r *ᵥ v) v
    rw [E_unit _ hH hsq] at hcs
    set S := ∑ i, Complex.normSq (v i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h1 : ‖herm (Hpk k r) v v‖ ^ 2 ≤ S ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, sq]
      exact hcs
    have h2 : ‖herm (Hpk k r) v v‖ ≤ S := (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp h1
    exact (Complex.re_le_norm _).trans h2

/- English proof (translation)
Introduce `k r g hg`. Establish `hH` using `GBasic.Hpk_herm k r`. Establish `hsq` using `GBasic.Hpk_sq k r`. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]`. Establish `hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r` using `Matrix.inv_eq_left_inv hleft`. Establish `hright : g * g⁻¹ = 1`. Rewrite using `[hinv]`. Use `first`.

Consider the case `exact Matrix.mul_eq_one_comm.mp hleft`. Consider the case `exact mul_eq_one_comm.mp hleft`. Establish `hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j)`. Establish `he : ∀ i j, Complex.normSq (g⁻¹ i j) = Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i))`. Introduce `i j`.

Rewrite using `[hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul, Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [he]`. Set `σ : Equiv.Perm (Fin (2 * r + k + 1))` to `Function.Involutive.toPerm _ (GBasic.sig_sig k r)`. Rewrite using `[Finset.sum_comm]`.

Use `Fintype.sum_equiv σ _ _ fun j => ?_` and prove the remaining obligations. Conclude with `Fintype.sum_equiv σ _ _ fun i => rfl`. Use `⟨by simp only [B.gN, hsum], ?_⟩` and prove the remaining obligations. Use `set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩`. Establish `hcs` using `euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))`.

Establish `h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1`. Use `congrFun (congrFun hright i0) i0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Simplify `this` using `[dotProduct]`. Rewrite `hcs` using `[h1, Complex.normSq_one]`.

Establish `hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j)` using `fun h => Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)`. Establish `hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2`. Rewrite using `[hgN, Finset.sum_comm]`. Conclude with `Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j)) (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)`. Establish `hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2`.

Rewrite using `[hgN]`. Simplify using `only [Complex.star_def, Complex.normSq_conj]`. Conclude with `Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l)) (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)`. Establish `hN0 : 0 ≤ B.gN g` using `Real.sqrt_nonneg _`. Establish `hEq : B.gN g⁻¹ = B.gN g` using `by simp only [B.gN, hsum]`.

Rewrite `hA` using `[hEq]`. Establish `h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2` using `hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (sq_nonneg _))`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `: B.gN g ^ 2 * B.gN g ^ 2 < 1`.

Establish `h5 : B.gN g ^ 2 < 1` using `by nlinarith`. Use polynomial arithmetic with `[sq_nonneg (B.gN g)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_of_inverse : C2.NormInv := by
  intro k r g hg
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg

  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hleft
  have hright : g * g⁻¹ = 1 := by
    rw [hinv]
    first
    | exact Matrix.mul_eq_one_comm.mp hleft
    | exact mul_eq_one_comm.mp hleft
  have hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j) := by
    have he : ∀ i j, Complex.normSq (g⁻¹ i j) =
        Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i)) := by
      intro i j
      rw [hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul,
        Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]
      ring
    simp only [he]
    let σ : Equiv.Perm (Fin (2 * r + k + 1)) :=
      Function.Involutive.toPerm _ (GBasic.sig_sig k r)
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv σ _ _ fun j => ?_
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  refine ⟨by simp only [B.gN, hsum], ?_⟩

  set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hcs := euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))
  have h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1 := by
    have := congrFun (congrFun hright i0) i0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [dotProduct] using this
  rw [h1, Complex.normSq_one] at hcs
  have hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j) := fun h =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2 := by
    rw [hgN, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j))
      (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2 := by
    rw [hgN]
    simp only [Complex.star_def, Complex.normSq_conj]
    exact Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hN0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hEq : B.gN g⁻¹ = B.gN g := by simp only [B.gN, hsum]
  rw [hEq] at hA
  have h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2 :=
    hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
      (sq_nonneg _))
  by_contra hlt
  push_neg at hlt
  have : B.gN g ^ 2 * B.gN g ^ 2 < 1 := by
    have h5 : B.gN g ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (B.gN g)]
  linarith

end Formalism.FourierDecayAlt.P
