import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.CartanRel

/- English proof (translation)
Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_multiply]`.
-/
theorem J_mul_J (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

/- English proof (translation)
Simplify using `[Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]`.
-/
theorem J_conjTranspose (p q : ℕ) : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Establish `hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)))`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hJ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify using the standard rewrite rules. Simplify using `[h (Sum.inl i) (Sum.inr j) (by simp [sameBlock])]`. Simplify using `[h (Sum.inr i) (Sum.inl j) (by simp [sameBlock])]`. Simplify using the standard rewrite rules.

Introduce `h i j hij`. Establish `e` using `congrFun (congrFun h i) j`. Rewrite `e` using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify using `[sameBlock] at hij`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr] at e`. Take the linear combination `(-1 / 2 : ℂ) * e`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at e`. Take the linear combination `(1 / 2 : ℂ) * e`. Simplify using `[sameBlock] at hij`.
-/
theorem isKC_iff {p q : ℕ} (b : Mat p q) : IsKC b ↔ b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ]
  constructor
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with i | i <;> rcases j with j | j
    · simp
    · simp [h (Sum.inl i) (Sum.inr j) (by simp [sameBlock])]
    · simp [h (Sum.inr i) (Sum.inl j) (by simp [sameBlock])]
    · simp
  · intro h i j hij
    have e := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    rcases i with i | i <;> rcases j with j | j
    · simp [sameBlock] at hij
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (-1 / 2 : ℂ) * e
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (1 / 2 : ℂ) * e
    · simp [sameBlock] at hij

/- English proof (translation)
Introduce `n p q hn A G t hG hA ht`. Establish `hJ` using `J_mul_J p q`. Establish `hJc` using `J_conjTranspose p q`. Generalize the expression as in `hJdef : Formalism.UG.Jpq p q = J at hJ hJc hA ht`. Choose the witnesses or unpack the hypotheses as in `⟨B, hBA, hAB⟩ : ∃ B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ, B * A = 1 ∧ A * B = 1 := by`.

Establish `h1 : (G⁻¹ * (Aᴴ * J)) * A = 1`. Rewrite using `[Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (Ne.isUnit hG)]`. Conclude with `⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1⟩`. Establish `cancel : ∀ x y : Matrix (Fin n) (Fin n) ℂ, A * x = A * y → x = y`. Introduce `x y h`.

Use `congrArg (B * ·) h` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, hBA, Matrix.one_mul]`. Establish `hJJ : J * (J * A) = A` using `by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Establish `hGt : G * t = Aᴴ * A`. Rewrite using `[← hA, Matrix.mul_assoc, ← ht, Matrix.mul_assoc, hJJ]`.

Use `⟨⟨?_, ?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Apply `cancel` to reduce the goal to its premises. Rewrite using `[← Matrix.mul_assoc, ← ht, Matrix.mul_assoc, ← ht, hJJ, Matrix.mul_one]`. Rewrite using `[Matrix.mul_assoc, hGt, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← ht, Matrix.conjTranspose_mul, hJc, hA]`. Rewrite using `[hGt]`.

Use `Matrix.PosDef.conjTranspose_mul_self A ?_` and prove the remaining obligations. Introduce `x y h`. Use `congrArg (B.mulVec) h` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]`. Introduce and unpack `⟨b, hb, hbA⟩`.

Rewrite `hb` using `[isKC_iff, hJdef]`. Apply `cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Use `⟨A * g * B, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[isKC_iff, hJdef]`. Establish `hBJ : B * J = t * B`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hAB, Matrix.mul_one]`. Use `_ = t * B := by rw [ht, ← Matrix.mul_assoc, hBA, Matrix.one_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hBJ]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = A * t * (g * B) := by rw [h.eq]; simp only [Matrix.mul_assoc]`. Use `_ = J * (A * g * B) := by rw [← ht]; simp only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.mul_assoc, hBA, Matrix.mul_one]`.
-/
theorem cartan_rel : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  intro n p q hn A G t hG hA ht
  have hJ := J_mul_J p q
  have hJc := J_conjTranspose p q
  generalize hJdef : Formalism.UG.Jpq p q = J at hJ hJc hA ht
  obtain ⟨B, hBA, hAB⟩ : ∃ B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ, B * A = 1 ∧ A * B = 1 := by
    have h1 : (G⁻¹ * (Aᴴ * J)) * A = 1 := by
      rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (Ne.isUnit hG)]
    exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1⟩
  have cancel : ∀ x y : Matrix (Fin n) (Fin n) ℂ, A * x = A * y → x = y := by
    intro x y h
    have := congrArg (B * ·) h
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using this
  have hJJ : J * (J * A) = A := by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hGt : G * t = Aᴴ * A := by
    rw [← hA, Matrix.mul_assoc, ← ht, Matrix.mul_assoc, hJJ]
  refine ⟨⟨?_, ?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  · apply cancel
    rw [← Matrix.mul_assoc, ← ht, Matrix.mul_assoc, ← ht, hJJ, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hGt, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← ht,
      Matrix.conjTranspose_mul, hJc, hA]
  · rw [hGt]
    refine Matrix.PosDef.conjTranspose_mul_self A ?_
    intro x y h
    have := congrArg (B.mulVec) h
    simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] using this
  · rintro ⟨b, hb, hbA⟩
    rw [isKC_iff, hJdef] at hb
    apply cancel
    calc A * (g * t) = b * (J * A) := by rw [← Matrix.mul_assoc, ← hbA, Matrix.mul_assoc, ← ht]
      _ = J * (A * g) := by rw [← Matrix.mul_assoc, hb, Matrix.mul_assoc, hbA]
      _ = A * (t * g) := by rw [← Matrix.mul_assoc, ht, Matrix.mul_assoc]
  · intro h
    refine ⟨A * g * B, ?_, ?_⟩
    · rw [isKC_iff, hJdef]
      have hBJ : B * J = t * B := by
        calc B * J = B * (J * A) * B := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, hAB, Matrix.mul_one]
          _ = t * B := by rw [ht, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
      calc A * g * B * J = A * (g * t) * B := by
            rw [Matrix.mul_assoc, hBJ]; simp only [Matrix.mul_assoc]
        _ = A * t * (g * B) := by rw [h.eq]; simp only [Matrix.mul_assoc]
        _ = J * (A * g * B) := by rw [← ht]; simp only [Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hBA, Matrix.mul_one]

end GlobalTheory.FockCompare.CartanRel
