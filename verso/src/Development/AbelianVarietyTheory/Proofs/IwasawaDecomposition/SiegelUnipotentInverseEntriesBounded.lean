import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `n`. Use `⟨(Nat.factorial n : ℝ), ?_⟩` and prove the remaining obligations. Introduce `u hdiag hlow hup`. Establish `hbt : u.BlockTriangular id` using `fun i j hij => hlow i j hij`. Establish `hdet : u.det = 1`.

Rewrite using `[Matrix.det_of_upperTriangular hbt]`. Simplify using `[hdiag]`. Establish `hunit : IsUnit u.det` using `by rw [hdet]; exact isUnit_one`. Use `⟨u⁻¹, Matrix.nonsing_inv_mul u hunit, Matrix.mul_nonsing_inv u hunit, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Use `letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hbt hij`. Introduce `i j`. Establish `hinv : u⁻¹ = u.adjugate`. Rewrite using `[Matrix.inv_def, hdet]`.

Simplify using the standard rewrite rules. Rewrite using `[hinv, Matrix.adjugate_apply]`. Establish `hb : ∀ a b, |(u.updateRow j (Pi.single i 1)) a b| ≤ 1`. Introduce `a b`. Distinguish the cases in `ha : a = j`.

Substitute `ha` using the available equality. Rewrite using `[Matrix.updateRow_self]`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hb]`. Rewrite using `[Matrix.updateRow_ne ha]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Combine the linear relations using `[hup a b h]`. Substitute `h` using the available equality.

Simplify using `[hdiag]`. Simplify using `[hlow a b h]`. Use `Matrix.det_le (abv := AbsoluteValue.abs) hb` as an intermediate fact. Simplify using `using this`.
-/
theorem siegel_unipotent_inv_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  intro n
  refine ⟨(Nat.factorial n : ℝ), ?_⟩
  intro u hdiag hlow hup
  have hbt : u.BlockTriangular id := fun i j hij => hlow i j hij
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    simp [hdiag]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  refine ⟨u⁻¹, Matrix.nonsing_inv_mul u hunit, Matrix.mul_nonsing_inv u hunit, ?_, ?_⟩
  · intro i j hij
    letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
    exact Matrix.blockTriangular_inv_of_blockTriangular hbt hij
  · intro i j
    have hinv : u⁻¹ = u.adjugate := by
      rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have hb : ∀ a b, |(u.updateRow j (Pi.single i 1)) a b| ≤ 1 := by
      intro a b
      by_cases ha : a = j
      · subst ha
        rw [Matrix.updateRow_self]
        by_cases hb : b = i
        · subst hb; simp
        · simp [Pi.single_apply, hb]
      · rw [Matrix.updateRow_ne ha]
        rcases lt_trichotomy a b with h | h | h
        · linarith [hup a b h]
        · subst h; simp [hdiag]
        · simp [hlow a b h]
    have := Matrix.det_le (abv := AbsoluteValue.abs) hb
    simpa using this

end GlobalTheory
