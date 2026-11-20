import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SumSqGe

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
Take `⟨hpu, hpM, -, -⟩` from `hp`. Establish `hPp : mt p⁻¹ w * mt p w = 1` using `mt_inv_mul p w`. Take `⟨hPu, hPd⟩` from `inv_upper (hpu w) hPp`. Establish `hD : mt (dg L N s hs)⁻¹ w = diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ)`. Establish `h1` using `mt_inv_mul (dg L N s hs) w`.

Establish `h2 : mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)` using `rfl`. Rewrite `h1` using `[h2]`. Establish `h3 : (diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) * (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ)) = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hK : mt k⁻¹ w ∈ unitaryGroup (Fin N) ℂ`. Establish `hU` using `hk w`.

Establish `h1 : mt k⁻¹ w * mt k w = 1` using `mt_inv_mul k w`. Establish `h2 : mt k⁻¹ w = star (mt k w)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Unitary.mul_star_self_of_mem hU, Matrix.mul_one]`. Use `_ = star (mt k w) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Rewrite using `[h2]`. Conclude with `Unitary.star_mem hU`. Establish `hQ : mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w = mt k⁻¹ w *ᵥ (mt (dg L N s hs)⁻¹ w *ᵥ (mt p⁻¹ w *ᵥ (mt c⁻¹ w *ᵥ toR y w)))`. Simplify using `only [_root_.mul_inv_rev, mt_mul, mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[hQ, sum_norm_unitary hK]`.

Use `le_trans ?_ (single_le_sum_sq _ i0)` and prove the remaining obligations. Establish `hzero : ∀ j, i0 < j → ((z w)⁻¹ • fun a => w.embedding ((gi g *ᵥ toL y) a)) j = 0`. Introduce `j hj`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hgt j hj, map_zero, mul_zero]`.

Rewrite using `[cinv_vec hN hc y w, hD, mulVec_diagonal, mulVec_upper hPu hzero]`. Establish `hne : mt p w i0 i0 ≠ 0`. Introduce `h`. Establish `h1` using `hPd i0`. Rewrite `h1` using `[h, mul_zero]`.

Conclude with `zero_ne_one h1`. Establish `hpos : 0 < ‖mt p w i0 i0‖` using `norm_pos_iff.2 hne`. Establish `hM : 0 < M` using `lt_of_lt_of_le hpos (hpM w i0 i0)`. Establish `hPi : M⁻¹ ≤ ‖mt p⁻¹ w i0 i0‖`. Establish `h3 : ‖mt p⁻¹ w i0 i0‖ * ‖mt p w i0 i0‖ = 1` using `by rw [← norm_mul, hPd i0, norm_one]`.

Rewrite using `[eq_inv_of_mul_eq_one_left h3]`. Conclude with `inv_anti₀ hpos (hpM w i0 i0)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_inv]`. Establish `hM' : 0 ≤ M⁻¹` using `inv_nonneg.2 hM.le`. Use `pow_le_pow_left₀ (by positivity) ?_ 2` and prove the remaining obligations.

Rewrite using `[mul_assoc]`. Use `gcongr`.
-/
theorem primal_place (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding)
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    (y : Lat L N) {i0 : Fin N} (hgt : ∀ j, i0 < j → (gi g *ᵥ toL y) j = 0) (w : InfinitePlace L) :
    (Real.exp (-s i0) * M⁻¹ * (‖z w‖⁻¹ * ‖w.embedding ((gi g *ᵥ toL y) i0)‖)) ^ 2 ≤
      ∑ i, ‖(mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  obtain ⟨hpu, hpM, -, -⟩ := hp
  have hPp : mt p⁻¹ w * mt p w = 1 := mt_inv_mul p w
  obtain ⟨hPu, hPd⟩ := inv_upper (hpu w) hPp
  have hD : mt (dg L N s hs)⁻¹ w = diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ) := by
    have h1 := mt_inv_mul (dg L N s hs) w
    have h2 : mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) := rfl
    rw [h2] at h1
    have h3 : (diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) * (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    calc mt (dg L N s hs)⁻¹ w
        = mt (dg L N s hs)⁻¹ w * ((diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) *
            (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ))) := by rw [h3, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hK : mt k⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
    have hU := hk w
    have h1 : mt k⁻¹ w * mt k w = 1 := mt_inv_mul k w
    have h2 : mt k⁻¹ w = star (mt k w) := by
      calc mt k⁻¹ w = mt k⁻¹ w * (mt k w * star (mt k w)) := by
            rw [Unitary.mul_star_self_of_mem hU, Matrix.mul_one]
        _ = star (mt k w) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [h2]
    exact Unitary.star_mem hU
  have hQ : mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w =
      mt k⁻¹ w *ᵥ (mt (dg L N s hs)⁻¹ w *ᵥ (mt p⁻¹ w *ᵥ (mt c⁻¹ w *ᵥ toR y w))) := by
    simp only [_root_.mul_inv_rev, mt_mul, mulVec_mulVec, Matrix.mul_assoc]
  rw [hQ, sum_norm_unitary hK]
  refine le_trans ?_ (single_le_sum_sq _ i0)
  have hzero : ∀ j, i0 < j → ((z w)⁻¹ • fun a => w.embedding ((gi g *ᵥ toL y) a)) j = 0 := by
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hgt j hj, map_zero, mul_zero]
  rw [cinv_vec hN hc y w, hD, mulVec_diagonal, mulVec_upper hPu hzero]
  have hne : mt p w i0 i0 ≠ 0 := by
    intro h
    have h1 := hPd i0
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hpos : 0 < ‖mt p w i0 i0‖ := norm_pos_iff.2 hne
  have hM : 0 < M := lt_of_lt_of_le hpos (hpM w i0 i0)
  have hPi : M⁻¹ ≤ ‖mt p⁻¹ w i0 i0‖ := by
    have h3 : ‖mt p⁻¹ w i0 i0‖ * ‖mt p w i0 i0‖ = 1 := by rw [← norm_mul, hPd i0, norm_one]
    rw [eq_inv_of_mul_eq_one_left h3]
    exact inv_anti₀ hpos (hpM w i0 i0)
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_inv]
  have hM' : 0 ≤ M⁻¹ := inv_nonneg.2 hM.le
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [mul_assoc]
  gcongr

/- English proof (translation)
Take `⟨hpu, hpM, hpm, -⟩` from `hp`. Establish `hKT : (mt k w)ᵀ ∈ unitaryGroup (Fin N) ℂ`. Rewrite using `[mem_unitaryGroup_iff]`. Establish `h1 : star (mt k w) * mt k w = 1` using `Unitary.star_mul_self_of_mem (hk w)`. Establish `h2 : star ((mt k w)ᵀ) = (star (mt k w))ᵀ`.

Use extensionality with `i j`. Simplify using `[star_eq_conjTranspose]`. Rewrite using `[h2, ← transpose_mul, h1, transpose_one]`. Establish `hQ : (mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w = (mt k w)ᵀ *ᵥ ((mt (dg L N s hs) w)ᵀ *ᵥ ((mt p w)ᵀ *ᵥ ((mt c w)ᵀ *ᵥ toR y w)))`. Simplify using `only [mt_mul, transpose_mul, mulVec_mulVec, Matrix.mul_assoc]`.

Establish `hD : (mt (dg L N s hs) w)ᵀ = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)`. Rewrite using `[show mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) from rfl, diagonal_transpose]`. Establish `hlow : ∀ a b : Fin N, a < b → (mt p w)ᵀ a b = 0` using `fun a b hab => by`. Rewrite using `[transpose_apply]`. Conclude with `hpu w hab`.

Establish `hzero : ∀ j, j < i1 → (z w • fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) j = 0`. Introduce `j hj`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hlt j hj, map_zero, mul_zero]`. Rewrite using `[hQ, sum_norm_unitary hKT]`.

Use `le_trans ?_ (single_le_sum_sq _ i1)` and prove the remaining obligations. Rewrite using `[cT_vec hc y w, hD, mulVec_diagonal, mulVec_lower hlow hzero, transpose_apply]`. Establish `hM : 0 ≤ M` using `(norm_nonneg _).trans (hpM w i1 i1)`. Establish `hM' : 0 ≤ M⁻¹` using `inv_nonneg.2 hM`. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`.

Use `pow_le_pow_left₀ (by positivity) ?_ 2` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `gcongr`. Conclude with `hpm w i1`.
-/
theorem dual_place {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding)
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    (y : Lat L N) {i1 : Fin N} (hlt : ∀ j, j < i1 → ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) j = 0)
    (w : InfinitePlace L) :
    (Real.exp (s i1) * M⁻¹ * (‖z w‖ * ‖w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) i1)‖)) ^ 2 ≤
      ∑ i, ‖((mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  obtain ⟨hpu, hpM, hpm, -⟩ := hp
  have hKT : (mt k w)ᵀ ∈ unitaryGroup (Fin N) ℂ := by
    rw [mem_unitaryGroup_iff]
    have h1 : star (mt k w) * mt k w = 1 := Unitary.star_mul_self_of_mem (hk w)
    have h2 : star ((mt k w)ᵀ) = (star (mt k w))ᵀ := by
      ext i j
      simp [star_eq_conjTranspose]
    rw [h2, ← transpose_mul, h1, transpose_one]
  have hQ : (mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w =
      (mt k w)ᵀ *ᵥ ((mt (dg L N s hs) w)ᵀ *ᵥ ((mt p w)ᵀ *ᵥ ((mt c w)ᵀ *ᵥ toR y w))) := by
    simp only [mt_mul, transpose_mul, mulVec_mulVec, Matrix.mul_assoc]
  have hD : (mt (dg L N s hs) w)ᵀ = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) := by
    rw [show mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) from rfl,
      diagonal_transpose]
  have hlow : ∀ a b : Fin N, a < b → (mt p w)ᵀ a b = 0 := fun a b hab => by
    rw [transpose_apply]
    exact hpu w hab
  have hzero : ∀ j, j < i1 → (z w • fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) j = 0 := by
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hlt j hj, map_zero, mul_zero]
  rw [hQ, sum_norm_unitary hKT]
  refine le_trans ?_ (single_le_sum_sq _ i1)
  rw [cT_vec hc y w, hD, mulVec_diagonal, mulVec_lower hlow hzero, transpose_apply]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hpM w i1 i1)
  have hM' : 0 ≤ M⁻¹ := inv_nonneg.2 hM
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [mul_assoc]
  gcongr
  exact hpm w i1

end PositivityTheory.KB.MomentRationality.Ht
