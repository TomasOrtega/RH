import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HmkFactor

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using the standard rewrite rules. Take `⟨B, rfl⟩` from `PIW.AdelClassFin.hmk_factor G hG`. Establish `hdetG : (Bᵀ * B).det = B.det ^ 2` using `by rw [det_mul, det_transpose, sq]`. Establish `hpos : 0 < (Bᵀ * B).det` using `hG.det_pos`.

Establish `hB : B.det ≠ 0`. Introduce `h0`. Rewrite `hpos` using `[hdetG, h0]`. Simplify using `at hpos`. Take `⟨c, hc, hbox⟩` from `PIW.AdelClassFin.hmk_box hN B hB`.

Use `set t := |B.det| ^ (1 / (N : ℝ)) with ht`. Use `set y := B *ᵥ fun j => (c j : ℝ) with hy`. Establish `hq : (fun i => (c i : ℝ)) ⬝ᵥ ((Bᵀ * B) *ᵥ fun i => (c i : ℝ)) = y ⬝ᵥ y`. Rewrite using `[← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]`. Establish `hsum : y ⬝ᵥ y ≤ 4 * N * t ^ 2`.

Establish `hi : ∀ i, y i * y i ≤ (2 * t) ^ 2`. Introduce `i`. Rewrite using `[← sq, ← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hbox i) 2`. Combine the equalities or inequalities in the displayed calculation.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : 1 ≤ 4 * N * t ^ 2` using `(h c hc).trans (hq.le.trans hsum)`. Establish `htN : t ^ N = |B.det|`. Rewrite using `[ht, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul, mul_comm 2 N, pow_mul, htN, sq_abs, hdetG]`.
-/
private theorem UpperTheory.V.KT.gramlow_fin (N : ℕ) (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef)
    (h : ∀ c : Fin N → ℤ, c ≠ 0 → 1 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))) :
    1 ≤ (4 * (N : ℝ)) ^ N * G.det := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨B, rfl⟩ := PIW.AdelClassFin.hmk_factor G hG
  have hdetG : (Bᵀ * B).det = B.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hpos : 0 < (Bᵀ * B).det := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h0
    rw [hdetG, h0] at hpos
    simp at hpos
  obtain ⟨c, hc, hbox⟩ := PIW.AdelClassFin.hmk_box hN B hB
  set t := |B.det| ^ (1 / (N : ℝ)) with ht
  set y := B *ᵥ fun j => (c j : ℝ) with hy
  have hq : (fun i => (c i : ℝ)) ⬝ᵥ ((Bᵀ * B) *ᵥ fun i => (c i : ℝ)) = y ⬝ᵥ y := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hsum : y ⬝ᵥ y ≤ 4 * N * t ^ 2 := by
    have hi : ∀ i, y i * y i ≤ (2 * t) ^ 2 := by
      intro i
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbox i) 2
    calc y ⬝ᵥ y = ∑ i, y i * y i := rfl
      _ ≤ ∑ _i : Fin N, (2 * t) ^ 2 := Finset.sum_le_sum fun i _ => hi i
      _ = 4 * N * t ^ 2 := by
        simp
        ring
  have h1 : 1 ≤ 4 * N * t ^ 2 := (h c hc).trans (hq.le.trans hsum)
  have htN : t ^ N = |B.det| := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
      inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_one]
  calc (1 : ℝ) = 1 ^ N := (one_pow N).symm
    _ ≤ (4 * N * t ^ 2) ^ N := pow_le_pow_left₀ zero_le_one h1 N
    _ = (4 * N) ^ N * (Bᵀ * B).det := by
      rw [mul_pow, ← pow_mul, mul_comm 2 N, pow_mul, htN, sq_abs, hdetG]

/- English proof (translation)
Introduce `ι _ _ G hG h`. Set `e : ι ≃ Fin (Fintype.card ι)` to `Fintype.equivFin ι`. Establish `hG' : (G.submatrix e.symm e.symm).PosDef` using `hG.submatrix e.symm.injective`. Rewrite using `[← det_submatrix_equiv_self e.symm G]`. Use `UpperTheory.V.KT.gramlow_fin _ _ hG' ?_` and prove the remaining obligations.

Introduce `c hc`. Establish `hc' : c ∘ e ≠ 0`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Simplify using `using congrFun h0 (e.symm i)`. Establish `key` using `h (c ∘ e) hc'`. Rewrite using `[submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]`. Conclude with `key`.
-/
theorem UpperTheory.V.KT.gramlow :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    (∀ c : ι → ℤ, c ≠ 0 → 1 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))) →
    1 ≤ (4 * (Fintype.card ι : ℝ)) ^ Fintype.card ι * G.det := by
  intro ι _ _ G hG h
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hG' : (G.submatrix e.symm e.symm).PosDef := hG.submatrix e.symm.injective
  rw [← det_submatrix_equiv_self e.symm G]
  refine UpperTheory.V.KT.gramlow_fin _ _ hG' ?_
  intro c hc
  have hc' : c ∘ e ≠ 0 := by
    intro h0
    apply hc
    funext i
    simpa using congrFun h0 (e.symm i)
  have key := h (c ∘ e) hc'
  rw [submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  exact key
