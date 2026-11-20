import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceA

open Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `hu : IsUnit B` using `(Matrix.isUnit_iff_isUnit_det B).2 (Ne.isUnit hB)`. Establish `hli : LinearIndependent ℝ B.row` using `Matrix.linearIndependent_rows_iff_isUnit.2 hu`. Set `b : Module.Basis (Fin m) ℝ (Fin m → ℝ)` to `basisOfPiSpaceOfLinearIndependent hli`. Establish `hb : (b : Fin m → Fin m → ℝ) = B.row` using `coe_basisOfPiSpaceOfLinearIndependent hli`. Establish `hpos : 0 < |B.det|` using `abs_pos.2 hB`.

Use `set t : ℝ := |B.det| ^ ((m : ℝ)⁻¹) with ht`. Establish `ht0 : 0 < t` using `Real.rpow_pos_of_pos hpos _`. Establish `htm : t ^ m = |B.det|` using `Real.rpow_inv_natCast_pow hpos.le hm.ne'`. Take `⟨x, hx, hx0, hxt⟩` from `ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le hm b ht0 (by`. Rewrite using `[htm, hb]`.

Conclude with `le_of_eq rfl)`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hx`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx0`.

Establish `hx' : ∑ i, c i • b i = (fun i => (c i : ℝ)) ᵥ* B`. Use extensionality with `j`. Simplify using `[hb, Matrix.vecMul, dotProduct, Finset.sum_apply]`. Rewrite `hxt` using `[hx']`. Establish `h1` using `h c hc`.

Rewrite `h1` using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]`. Use `set y := (fun i => (c i : ℝ)) ᵥ* B`. Establish `h2 : y ⬝ᵥ y ≤ m * t ^ 2`. Establish `: ∀ i ∈ (Finset.univ : Finset (Fin m)), y i * y i ≤ t ^ 2`. Introduce `i _`.

Establish `h3 : |y i| ≤ t` using `(norm_le_pi_norm y i).trans hxt`. Rewrite using `[← sq, ← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) h3 2`. Establish `h4` using `Finset.sum_le_sum this`. Simplify `h4` using `[dotProduct]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul, mul_comm 2 m, pow_mul, htm, sq_abs, det_mul, det_transpose, sq]`.
-/
theorem minkowski_det_bound_gram_of_det_ne_zero (m : ℕ) (hm : 0 < m) (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ (B * Bᵀ) *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * (B * Bᵀ).det := by
  classical
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (Ne.isUnit hB)
  have hli : LinearIndependent ℝ B.row := Matrix.linearIndependent_rows_iff_isUnit.2 hu
  let b : Module.Basis (Fin m) ℝ (Fin m → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (b : Fin m → Fin m → ℝ) = B.row := coe_basisOfPiSpaceOfLinearIndependent hli
  have hpos : 0 < |B.det| := abs_pos.2 hB
  set t : ℝ := |B.det| ^ ((m : ℝ)⁻¹) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hpos _
  have htm : t ^ m = |B.det| := Real.rpow_inv_natCast_pow hpos.le hm.ne'
  obtain ⟨x, hx, hx0, hxt⟩ := ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le hm b ht0 (by
    rw [htm, hb]; exact le_of_eq rfl)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hx0
  have hx' : ∑ i, c i • b i = (fun i => (c i : ℝ)) ᵥ* B := by
    ext j
    simp [hb, Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [hx'] at hxt
  have h1 := h c hc
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at h1
  set y := (fun i => (c i : ℝ)) ᵥ* B
  have h2 : y ⬝ᵥ y ≤ m * t ^ 2 := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin m)), y i * y i ≤ t ^ 2 := by
      intro i _
      have h3 : |y i| ≤ t := (norm_le_pi_norm y i).trans hxt
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have h4 := Finset.sum_le_sum this
    simpa [dotProduct] using h4
  calc a ^ m ≤ (m * t ^ 2) ^ m := pow_le_pow_left₀ ha (h1.trans h2) m
    _ = (m : ℝ) ^ m * (B * Bᵀ).det := by
      rw [mul_pow, ← pow_mul, mul_comm 2 m, pow_mul, htm, sq_abs, det_mul, det_transpose, sq]

/- English proof (translation)
Use `open MatrixOrder in`. Take `⟨C, hC⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hG.posSemidef.nonneg`. Establish `hC' : G = Cᵀ * Cᵀᵀ`. Rewrite using `[hC, transpose_transpose, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]`. Establish `hd` using `hG.det_pos`.

Establish `hB : (Cᵀ).det ≠ 0`. Introduce `h0`. Rewrite `hd` using `[hC', det_mul, h0, zero_mul]`. Conclude with `lt_irrefl _ hd`. Rewrite `h`, the goal using `[hC']`.

Conclude with `minkowski_det_bound_gram_of_det_ne_zero m hm _ hB a ha h`.
-/
theorem minkowski_det_bound_posDef (m : ℕ) (hm : 0 < m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosDef) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * G.det := by
  open MatrixOrder in
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hG.posSemidef.nonneg
  have hC' : G = Cᵀ * Cᵀᵀ := by
    rw [hC, transpose_transpose, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hd := hG.det_pos
  have hB : (Cᵀ).det ≠ 0 := by
    intro h0
    rw [hC', det_mul, h0, zero_mul] at hd
    exact lt_irrefl _ hd
  rw [hC'] at h ⊢
  exact minkowski_det_bound_gram_of_det_ne_zero m hm _ hB a ha h

/- English proof (translation)
Introduce `m G hG a ha h`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using the standard rewrite rules. Establish `key : ∀ ε : ℝ, 0 < ε → a ^ m ≤ (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det`. Introduce `ε hε`.

Use `minkowski_det_bound_posDef m hm _ (Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hε)) a ha ?_` and prove the remaining obligations. Introduce `z hz`. Use `(h z hz).trans ?_` and prove the remaining obligations. Rewrite using `[add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul]`. Establish `: 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (fun i => (z i : ℝ))` using `Finset.sum_nonneg fun i _ => mul_self_nonneg _`.

Use `mul_nonneg hε.le this` as an intermediate fact. Simplify using `using this`. Establish `hc : Continuous fun ε : ℝ => (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det` using `continuous_const.mul (Continuous.matrix_det (by fun_prop))`. Establish `ht` using `(hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))`. Use `ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)` as an intermediate fact.

Simplify using `using this`.
-/
theorem minkowski_det_bound_posSemidef :
    ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → ∀ a : ℝ, 0 ≤ a →
      (∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) →
      a ^ m ≤ (m : ℝ) ^ m * G.det := by
  intro m G hG a ha h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have key : ∀ ε : ℝ, 0 < ε →
      a ^ m ≤ (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det := by
    intro ε hε
    refine minkowski_det_bound_posDef m hm _
      (Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hε)) a ha ?_
    intro z hz
    refine (h z hz).trans ?_
    rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul]
    have : 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (fun i => (z i : ℝ)) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have := mul_nonneg hε.le this
    simpa using this
  have hc : Continuous fun ε : ℝ =>
      (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det :=
    continuous_const.mul (Continuous.matrix_det (by fun_prop))
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  simpa using this

end GlobalTheory
