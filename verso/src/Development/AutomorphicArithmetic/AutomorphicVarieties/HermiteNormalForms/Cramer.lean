import Mathlib

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private lemma cs_vec {N : ℕ} (x y : Fin N → ℂ) (hx : (star x ⬝ᵥ x).re ≤ 1)
    (hy : (star y ⬝ᵥ y).re ≤ 1) : ‖star x ⬝ᵥ y‖ ≤ 1 := by
  have key : ∀ u v : Fin N → ℂ, star u ⬝ᵥ v =
      inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 v) := by
    intro u v
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have nb : ∀ u : Fin N → ℂ, (star u ⬝ᵥ u).re ≤ 1 →
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ≤ 1 := by
    intro u hu
    rw [key] at hu
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))
    have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ^ 2 ≤ 1 := by
      rw [← h]; exact hu
    nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))]
  rw [key]
  refine (norm_inner_le_norm _ _).trans ?_
  exact mul_le_one₀ (nb x hx) (norm_nonneg _) (nb y hy)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private lemma cs_form {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef)
    (x y : Fin N → ℂ) (hx : (star x ⬝ᵥ (G *ᵥ x)).re ≤ 1)
    (hy : (star y ⬝ᵥ (G *ᵥ y)).re ≤ 1) : ‖star x ⬝ᵥ (G *ᵥ y)‖ ≤ 1 := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  have key : ∀ u v : Fin N → ℂ, star u ⬝ᵥ (G *ᵥ v) = star (B *ᵥ u) ⬝ᵥ (B *ᵥ v) := by
    intro u v
    rw [hB, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose]
  rw [key] at hx hy ⊢
  exact cs_vec _ _ hx hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KT.cramer :
    ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (c : Fin N → ℂ), G.PosSemidef → (∀ a, (G a a).re ≤ 1) →
    (star c ⬝ᵥ (G *ᵥ c)).re ≤ 1 → ∀ a, ‖G.det‖ * ‖c a‖ ≤ (N : ℝ) ^ N := by
  intro N G c hG hd hc a
  have hs : ∀ (i : Fin N) (v : Fin N → ℂ), star (Pi.single i (1 : ℂ) : Fin N → ℂ) ⬝ᵥ v = v i := by
    intro i v
    simp [← Pi.single_star]
  have he : ∀ i j : Fin N, star (Pi.single i (1 : ℂ) : Fin N → ℂ) ⬝ᵥ
      (G *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)) = G i j := by
    intro i j
    rw [hs]; simp
  have h1 : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j
    rw [← he]
    exact cs_form G hG _ _ (by rw [he]; exact hd i) (by rw [he]; exact hd j)
  have h2 : ∀ i, ‖(G *ᵥ c) i‖ ≤ 1 := by
    intro i
    rw [← hs i (G *ᵥ c)]
    exact cs_form G hG _ _ (by rw [he]; exact hd i) hc
  have h3 : G.det * c a = (G.updateCol a (G *ᵥ c)).det := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul]
    simp [smul_mulVec]
  rw [← norm_mul, h3]
  have h4 := Matrix.det_le (A := G.updateCol a (G *ᵥ c)) (abv := NormedField.toAbsoluteValue ℂ)
    (x := 1) (by
      intro i j
      change ‖G.updateCol a (G *ᵥ c) i j‖ ≤ 1
      rw [updateCol_apply]
      split_ifs
      · exact h2 i
      · exact h1 i j)
  refine le_trans h4 ?_
  simp only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one]
  exact_mod_cast Nat.factorial_le_pow N
