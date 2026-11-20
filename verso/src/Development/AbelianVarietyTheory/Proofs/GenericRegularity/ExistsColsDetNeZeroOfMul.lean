import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Establish `hu : IsUnit (π.submatrix ι κ).det` using `isUnit_iff_ne_zero.mpr hd`. Establish `hC : π.submatrix id κ = π * (1 : Matrix (Fin n) (Fin n) Ω).submatrix id κ`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hA : π.submatrix ι κ = (1 : Matrix (Fin n) (Fin n) Ω).submatrix ι id * π.submatrix id κ`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hrA : (π.submatrix ι κ).rank = r`. Use `Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)` as an intermediate fact. Simplify using `using this`.

Establish `hle : LinearMap.range (π.submatrix id κ).mulVecLin ≤ LinearMap.range π.mulVecLin`. Rewrite using `[hC, Matrix.mulVecLin_mul]`. Conclude with `LinearMap.range_comp_le_range _ _`. Establish `hr : π.rank ≤ (π.submatrix id κ).rank`. Rewrite using `[hπ]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Matrix.rank_mul_le_right _ _`. Establish `heq` using `Submodule.eq_of_le_of_finrank_le hle hr`. Establish `hcol : ∀ j : Fin n, ∃ c : Fin r → Ω, (π.submatrix id κ) *ᵥ c = fun i => π i j`. Introduce `j`.

Establish `: (fun i => π i j) ∈ LinearMap.range π.mulVecLin` using `⟨Pi.single j 1, by ext i; simp⟩`. Rewrite `this` using `[← heq]`. Conclude with `this`. Use `choose c hc using hcol`. Use `set X : Matrix (Fin r) (Fin n) Ω := Matrix.of fun a j => c j a with hX`.

Establish `h1 : π = π.submatrix id κ * X`. Use extensionality with `i j`. Use `congrFun (hc j) i` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]`.

Establish `h2 : π.submatrix ι id = π.submatrix ι κ * X`. Use extensionality with `i j`. Use `congrFun (congrFun h1 (ι i)) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`. Rewrite using `[h2, Matrix.mul_assoc, ← Matrix.mul_assoc (π.submatrix ι κ)⁻¹, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`.

Conclude with `h1`.
-/
theorem eq_cols_mul_inv_minor_mul_rows {Ω : Type} [Field Ω] {n r : ℕ}
    (π : Matrix (Fin n) (Fin n) Ω) (hπ : π.rank = r) (ι κ : Fin r → Fin n)
    (hd : (π.submatrix ι κ).det ≠ 0) :
    π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id := by
  have hu : IsUnit (π.submatrix ι κ).det := isUnit_iff_ne_zero.mpr hd
  have hC : π.submatrix id κ = π * (1 : Matrix (Fin n) (Fin n) Ω).submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hA : π.submatrix ι κ
      = (1 : Matrix (Fin n) (Fin n) Ω).submatrix ι id * π.submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hrA : (π.submatrix ι κ).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hle : LinearMap.range (π.submatrix id κ).mulVecLin ≤ LinearMap.range π.mulVecLin := by
    rw [hC, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hr : π.rank ≤ (π.submatrix id κ).rank := by
    rw [hπ]
    calc r = (π.submatrix ι κ).rank := hrA.symm
      _ ≤ (π.submatrix id κ).rank := by
        conv_lhs => rw [hA]
        exact Matrix.rank_mul_le_right _ _
  have heq := Submodule.eq_of_le_of_finrank_le hle hr
  have hcol : ∀ j : Fin n, ∃ c : Fin r → Ω, (π.submatrix id κ) *ᵥ c = fun i => π i j := by
    intro j
    have : (fun i => π i j) ∈ LinearMap.range π.mulVecLin :=
      ⟨Pi.single j 1, by ext i; simp⟩
    rw [← heq] at this
    exact this
  choose c hc using hcol
  set X : Matrix (Fin r) (Fin n) Ω := Matrix.of fun a j => c j a with hX
  have h1 : π = π.submatrix id κ * X := by
    ext i j
    have := congrFun (hc j) i
    rw [← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  have h2 : π.submatrix ι id = π.submatrix ι κ * X := by
    ext i j
    have := congrFun (congrFun h1 (ι i)) j
    simpa [Matrix.mul_apply] using this
  rw [h2, Matrix.mul_assoc, ← Matrix.mul_assoc (π.submatrix ι κ)⁻¹, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]
  exact h1

/- English proof (translation)
Establish `hu : IsUnit (R * u).det` using `isUnit_iff_ne_zero.mpr hd`. Establish `hrA : (R * u).rank = r`. Use `Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)` as an intermediate fact. Simplify using `using this`. Establish `hrR : R.rank = r`.

Apply `le_antisymm` to reduce the goal to its premises. Simplify using `using Matrix.rank_le_card_height R`. Combine the equalities or inequalities in the displayed calculation. Take `⟨K, a, ha, hspan, hli⟩` from `exists_linearIndependent' Ω R.col`. Use `haveI : Fintype K := Fintype.ofInjective a ha`.

Establish `hcard : Fintype.card K = r`. Rewrite using `[← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hrR]`. Set `e : Fin r ≃ K` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨a ∘ e, ?_⟩` and prove the remaining obligations. Establish `h3 : LinearIndependent Ω (R.submatrix id (a ∘ e)).col` using `hli.comp e e.injective`.

Rewrite `h3` using `[Matrix.linearIndependent_cols_iff_isUnit]`. Conclude with `isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h3)`.
-/
theorem exists_cols_det_ne_zero_of_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (R : Matrix (Fin r) (Fin n) Ω) (u : Matrix (Fin n) (Fin r) Ω) (hd : (R * u).det ≠ 0) :
    ∃ κ : Fin r → Fin n, (R.submatrix id κ).det ≠ 0 := by
  have hu : IsUnit (R * u).det := isUnit_iff_ne_zero.mpr hd
  have hrA : (R * u).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hrR : R.rank = r := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height R
    · calc r = (R * u).rank := hrA.symm
        _ ≤ R.rank := Matrix.rank_mul_le_left _ _
  obtain ⟨K, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω R.col
  haveI : Fintype K := Fintype.ofInjective a ha
  have hcard : Fintype.card K = r := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hrR]
  let e : Fin r ≃ K := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have h3 : LinearIndependent Ω (R.submatrix id (a ∘ e)).col := hli.comp e e.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit] at h3
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h3)

/- English proof (translation)
Introduce `Ω _ n r π hπ ι`. Use `⟨fun κ hd => eq_cols_mul_inv_minor_mul_rows π hπ ι κ hd, fun u hu hd => ?_⟩` and prove the remaining obligations. Establish `h : π.submatrix ι id * u = u.submatrix ι id`. Use extensionality with `i j`. Use `congrFun (congrFun hu (ι i)) j` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply]`. Take `⟨κ, hκ⟩` from `exists_cols_det_ne_zero_of_mul (π.submatrix ι id) u (h ▸ hd)`. Conclude with `⟨κ, hκ⟩`.
-/
theorem rank_minor_factorisation :
    ∀ (Ω : Type) [Field Ω] (n r : ℕ) (π : Matrix (Fin n) (Fin n) Ω), π.rank = r → ∀ ι : Fin r → Fin n, (∀ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 → π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id) ∧ ∀ u : Matrix (Fin n) (Fin r) Ω, π * u = u → (u.submatrix ι id).det ≠ 0 → ∃ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 := by
  intro Ω _ n r π hπ ι
  refine ⟨fun κ hd => eq_cols_mul_inv_minor_mul_rows π hπ ι κ hd, fun u hu hd => ?_⟩
  have h : π.submatrix ι id * u = u.submatrix ι id := by
    ext i j
    have := congrFun (congrFun hu (ι i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := exists_cols_det_ne_zero_of_mul (π.submatrix ι id) u (h ▸ hd)
  exact ⟨κ, hκ⟩

end GlobalTheory
