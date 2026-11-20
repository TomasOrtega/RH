import Mathlib

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Establish `key : ∀ u v : Fin N → ℂ, star u ⬝ᵥ v = inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 v)`. Introduce `u v`. Rewrite using `[EuclideanSpace.inner_toLp_toLp, dotProduct_comm]`. Establish `nb : ∀ u : Fin N → ℂ, (star u ⬝ᵥ u).re ≤ 1 → ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ≤ 1`. Introduce `u hu`.

Rewrite `hu` using `[key]`. Establish `h` using `inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))`. Establish `h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ^ 2 ≤ 1`. Rewrite using `[← h]`. Conclude with `hu`.

Use polynomial arithmetic with `[norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))]`. Rewrite using `[key]`. Use `(norm_inner_le_norm _ _).trans ?_` and prove the remaining obligations. Conclude with `mul_le_one₀ (nb x hx) (norm_nonneg _) (nb y hy)`.
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
Use `open scoped MatrixOrder in`. Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg`. Establish `key : ∀ u v : Fin N → ℂ, star u ⬝ᵥ (G *ᵥ v) = star (B *ᵥ u) ⬝ᵥ (B *ᵥ v)`. Introduce `u v`. Rewrite using `[hB, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_eq_conjTranspose]`.

Rewrite `hx`, `hy`, the goal using `[key]`. Conclude with `cs_vec _ _ hx hy`.
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
Introduce `N G c hG hd hc a`. Establish `hs : ∀ (i : Fin N) (v : Fin N → ℂ), star (Pi.single i (1 : ℂ) : Fin N → ℂ) ⬝ᵥ v = v i`. Introduce `i v`. Simplify using `[← Pi.single_star]`. Establish `he : ∀ i j : Fin N, star (Pi.single i (1 : ℂ) : Fin N → ℂ) ⬝ᵥ (G *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)) = G i j`.

Introduce `i j`. Rewrite using `[hs]`. Simplify using the standard rewrite rules. Establish `h1 : ∀ i j, ‖G i j‖ ≤ 1`. Introduce `i j`.

Rewrite using `[← he]`. Conclude with `cs_form G hG _ _ (by rw [he]; exact hd i) (by rw [he]; exact hd j)`. Establish `h2 : ∀ i, ‖(G *ᵥ c) i‖ ≤ 1`. Introduce `i`. Rewrite using `[← hs i (G *ᵥ c)]`.

Conclude with `cs_form G hG _ _ (by rw [he]; exact hd i) hc`. Establish `h3 : G.det * c a = (G.updateCol a (G *ᵥ c)).det`. Rewrite using `[← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul]`. Simplify using `[smul_mulVec]`. Rewrite using `[← norm_mul, h3]`.

Establish `h4` using `Matrix.det_le (A := G.updateCol a (G *ᵥ c)) (abv := NormedField.toAbsoluteValue ℂ) (x := 1) (by`. Introduce `i j`. Express the relevant statement in the definitionally equal form `‖G.updateCol a (G *ᵥ c) i j‖ ≤ 1`. Rewrite using `[updateCol_apply]`. Use `split_ifs`.

Conclude with `h2 i`. Conclude with `h1 i j)`. Use `le_trans h4 ?_` and prove the remaining obligations. Simplify using `only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one]`. Conclude with `Nat.factorial_le_pow N` after adjusting the coercions.
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
