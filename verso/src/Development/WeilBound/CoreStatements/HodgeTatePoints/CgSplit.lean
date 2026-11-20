import Mathlib

namespace PositivityTheory.HtPt.Cg

open Matrix

/- English proof (translation)
Establish `hi : LinearMap.ker (Matrix.toLin' (M.map (IsLocalRing.residue A))) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `u hu`. Conclude with `h u (by simpa using hu)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hi`.

Establish `h1 : LinearMap.toMatrix' g * M.map (IsLocalRing.residue A) = 1`. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis. Use `choose l hl using fun i j => IsLocalRing.residue_surjective (LinearMap.toMatrix' g i j)`. Establish `h2 : (Matrix.of l * M).map (IsLocalRing.residue A) = 1`.

Rewrite using `[Matrix.map_mul, ← h1]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `hl i j`. Establish `h3 : IsUnit (Matrix.of l * M).det`.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, h2, det_one]`. Conclude with `one_ne_zero`. Conclude with `⟨(Matrix.of l * M)⁻¹ * Matrix.of l, by rw [Matrix.mul_assoc, nonsing_inv_mul _ h3]⟩`.
-/
theorem left_inv_of_residue {A : Type} [CommRing A] [IsLocalRing A] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n A)
    (h : ∀ u, (M.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) : ∃ N : Matrix n m A, N * M = 1 := by
  have hi : LinearMap.ker (Matrix.toLin' (M.map (IsLocalRing.residue A))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    exact h u (by simpa using hu)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hi
  have h1 : LinearMap.toMatrix' g * M.map (IsLocalRing.residue A) = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  choose l hl using fun i j => IsLocalRing.residue_surjective (LinearMap.toMatrix' g i j)
  have h2 : (Matrix.of l * M).map (IsLocalRing.residue A) = 1 := by
    rw [Matrix.map_mul, ← h1]
    congr 1
    ext i j
    exact hl i j
  have h3 : IsUnit (Matrix.of l * M).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, h2, det_one]
    exact one_ne_zero
  exact ⟨(Matrix.of l * M)⁻¹ * Matrix.of l, by rw [Matrix.mul_assoc, nonsing_inv_mul _ h3]⟩

/- English proof (translation)
Introduce `A _ _ d h a S hiso hinj`. Take `⟨N, hN⟩` from `left_inv_of_residue (fromRows h a.transpose) (fun u hu => by`. Rewrite `hu` using `[fromRows_map, fromRows_mulVec]`. Conclude with `hinj u (funext fun i => congrFun hu (Sum.inl i)) (funext fun i => congrFun hu (Sum.inr i)))`. Take `⟨x, y, rfl⟩ : ∃ x y, N = fromCols x y` from `⟨_, _, (fromCols_toCols N).symm⟩`.

Rewrite `hN` using `[fromCols_mul_fromRows]`. Establish `hT : h.transpose * x.transpose + a * y.transpose = 1`. Use `congrArg Matrix.transpose hN` as an intermediate fact. Simplify `this` using `[transpose_add, transpose_mul]`. Use `set b := a - h.transpose * S with hb`.

Use `set s₁ := y.transpose`. Use `set s₂ := -(x.transpose + S * y.transpose) with hs₂`. Establish `e2 : b * s₁ - h.transpose * s₂ = 1`. Rewrite using `[← hT, hb, hs₂]`. Use `noncomm_ring`.

Establish `e0 : b * h - h.transpose * a.transpose = 0`. Rewrite using `[← hiso, hb]`. Use `noncomm_ring`. Use `set w := x * s₁ + y * s₂ with hw`. Establish `e1 : (x - w * b) * h + (y + w * h.transpose) * a.transpose = 1`.

Establish `: (x - w * b) * h + (y + w * h.transpose) * a.transpose = (x * h + y * a.transpose) - w * (b * h - h.transpose * a.transpose)` using `by noncomm_ring`. Rewrite using `[this, hN, e0]`. Simplify using the standard rewrite rules. Establish `e3 : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ = 0`. Establish `: (x - w * b) * s₁ + (y + w * h.transpose) * s₂ = (x * s₁ + y * s₂) - w * (b * s₁ - h.transpose * s₂)` using `by noncomm_ring`.

Rewrite using `[this, e2, ← hw]`. Simplify using the standard rewrite rules. Establish `hNM : fromBlocks (x - w * b) (y + w * h.transpose) b (-h.transpose) * fromBlocks h s₁ a.transpose s₂ = 1`. Rewrite using `[fromBlocks_multiply, e1, e3, ← fromBlocks_one]`. Use `congr 1`.

Rewrite using `[← e0]`. Use `noncomm_ring`. Rewrite using `[← e2]`. Use `noncomm_ring`. Establish `hMN` using `mul_eq_one_comm.1 hNM`.

Rewrite `hMN` using `[fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]`. Take `⟨f1, f2, f3, f4⟩` from `hMN`. Use `⟨_, _, s₁, s₂, e1, e2, f1, ?_, f3, ?_⟩` and prove the remaining obligations. Rewrite using `[← f2]`. Use `noncomm_ring`.

Rewrite using `[← f4]`. Use `noncomm_ring`.
-/
theorem split_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 := by
  intro A _ _ d h a S hiso hinj
  obtain ⟨N, hN⟩ := left_inv_of_residue (fromRows h a.transpose) (fun u hu => by
    rw [fromRows_map, fromRows_mulVec] at hu
    exact hinj u (funext fun i => congrFun hu (Sum.inl i)) (funext fun i => congrFun hu (Sum.inr i)))
  obtain ⟨x, y, rfl⟩ : ∃ x y, N = fromCols x y := ⟨_, _, (fromCols_toCols N).symm⟩
  rw [fromCols_mul_fromRows] at hN
  have hT : h.transpose * x.transpose + a * y.transpose = 1 := by
    have := congrArg Matrix.transpose hN
    simpa [transpose_add, transpose_mul] using this
  set b := a - h.transpose * S with hb
  set s₁ := y.transpose
  set s₂ := -(x.transpose + S * y.transpose) with hs₂
  have e2 : b * s₁ - h.transpose * s₂ = 1 := by
    rw [← hT, hb, hs₂]; noncomm_ring
  have e0 : b * h - h.transpose * a.transpose = 0 := by
    rw [← hiso, hb]; noncomm_ring
  set w := x * s₁ + y * s₂ with hw
  have e1 : (x - w * b) * h + (y + w * h.transpose) * a.transpose = 1 := by
    have : (x - w * b) * h + (y + w * h.transpose) * a.transpose =
      (x * h + y * a.transpose) - w * (b * h - h.transpose * a.transpose) := by noncomm_ring
    rw [this, hN, e0]; simp
  have e3 : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ = 0 := by
    have : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ =
      (x * s₁ + y * s₂) - w * (b * s₁ - h.transpose * s₂) := by noncomm_ring
    rw [this, e2, ← hw]; simp
  have hNM : fromBlocks (x - w * b) (y + w * h.transpose) b (-h.transpose) *
      fromBlocks h s₁ a.transpose s₂ = 1 := by
    rw [fromBlocks_multiply, e1, e3, ← fromBlocks_one]
    congr 1
    · rw [← e0]; noncomm_ring
    · rw [← e2]; noncomm_ring
  have hMN := mul_eq_one_comm.1 hNM
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hMN
  obtain ⟨f1, f2, f3, f4⟩ := hMN
  refine ⟨_, _, s₁, s₂, e1, e2, f1, ?_, f3, ?_⟩
  · rw [← f2]; noncomm_ring
  · rw [← f4]; noncomm_ring

end PositivityTheory.HtPt.Cg
