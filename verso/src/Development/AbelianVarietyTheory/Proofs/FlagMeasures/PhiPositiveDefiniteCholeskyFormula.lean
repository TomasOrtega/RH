import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow

open Matrix Finset Formalism.MainNotions.S
open scoped ComplexOrder

namespace GlobalTheory.Dec

/- English proof (translation)
Introduce `i j hij` and use `hb i j (OrderDual.toDual_lt_toDual.mp hij)`.
-/
private lemma blockTriangular_toDual_of_isLo {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) :
    b.BlockTriangular OrderDual.toDual :=
  fun i j hij => hb i j (OrderDual.toDual_lt_toDual.mp hij)

/- English proof (translation)
Introduce `_ _ hij` and use `hb (OrderDual.toDual_lt_toDual.mpr hij)`.
-/
private lemma isLo_of_blockTriangular_toDual {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.BlockTriangular OrderDual.toDual) : IsLo b :=
  fun _ _ hij => hb (OrderDual.toDual_lt_toDual.mpr hij)

/- English proof (translation)
Establish `hLi : (LDL.lowerInv hx).BlockTriangular OrderDual.toDual` using `fun i j hij => LDL.lowerInv_triangular hx (OrderDual.toDual_lt_toDual.mp hij)`. Establish `hL : (LDL.lower hx).BlockTriangular OrderDual.toDual` using `Matrix.blockTriangular_inv_of_blockTriangular hLi`. Establish `hD : (LDL.diag hx).PosDef`. Rewrite using `[LDL.diag_eq_lowerInv_conj]`. Use `hx.mul_mul_conjTranspose_same ?_` and prove the remaining obligations.

Introduce `v w hvw`. Establish `h` using `congrArg (fun u => u ᵥ* (LDL.lowerInv hx)⁻¹) hvw`. Simplify `h` using `[Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible]`. Establish `hd : ∀ i, 0 < LDL.diagEntries hx i` using `fun i => by`. Simplify `hD.diag_pos (i := i)` using `[LDL.diag]`.

Set `s : Fin n → ℂ` to `fun i => ((Real.sqrt (LDL.diagEntries hx i).re : ℝ) : ℂ)`. Establish `hs : ∀ i, s i * star (s i) = LDL.diagEntries hx i` using `fun i => by`. Take `⟨hre, him⟩` from `Complex.pos_iff.mp (hd i)`. Establish `hsq` using `Real.mul_self_sqrt hre.le`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `[s, Complex.mul_re, hsq]`. Simplify using `[s, Complex.mul_im, ← him]`. Use `⟨LDL.lower hx * Matrix.diagonal s, isLo_of_blockTriangular_toDual (hL.mul (Matrix.blockTriangular_diagonal s)), ?_⟩` and prove the remaining obligations. Establish `hDs : LDL.diag hx = Matrix.diagonal s * (Matrix.diagonal s)ᴴ`. Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`.

Unfold `LDL.diag`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hs i).symm`. Use `conv_lhs => rw [← LDL.lower_conj_diag hx, hDs]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem exists_isLo_mul_conjTranspose {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ x = b * bᴴ := by
  classical

  have hLi : (LDL.lowerInv hx).BlockTriangular OrderDual.toDual :=
    fun i j hij => LDL.lowerInv_triangular hx (OrderDual.toDual_lt_toDual.mp hij)
  have hL : (LDL.lower hx).BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hLi

  have hD : (LDL.diag hx).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    refine hx.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h := congrArg (fun u => u ᵥ* (LDL.lowerInv hx)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible] using h
  have hd : ∀ i, 0 < LDL.diagEntries hx i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  let s : Fin n → ℂ := fun i => ((Real.sqrt (LDL.diagEntries hx i).re : ℝ) : ℂ)
  have hs : ∀ i, s i * star (s i) = LDL.diagEntries hx i := fun i => by
    obtain ⟨hre, him⟩ := Complex.pos_iff.mp (hd i)
    have hsq := Real.mul_self_sqrt hre.le
    apply Complex.ext
    · simp [s, Complex.mul_re, hsq]
    · simp [s, Complex.mul_im, ← him]
  refine ⟨LDL.lower hx * Matrix.diagonal s,
    isLo_of_blockTriangular_toDual (hL.mul (Matrix.blockTriangular_diagonal s)), ?_⟩
  have hDs : LDL.diag hx = Matrix.diagonal s * (Matrix.diagonal s)ᴴ := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    unfold LDL.diag
    congr 1
    funext i
    exact (hs i).symm
  conv_lhs => rw [← LDL.lower_conj_diag hx, hDs]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `i`. Simplify using `[leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _)]`.
-/
theorem one_mem_Omega_leadMinor (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Omega n := by
  intro i
  simp [leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _)]

/- English proof (translation)
Establish `hdet : (b * bᴴ).det ≠ 0` using `hx.det_pos.ne'`. Establish `hb' : b.det ≠ 0` using `fun h => hdet (by rw [Matrix.det_mul, h, zero_mul])`. Rewrite `hb'` using `[Matrix.det_of_isLowerTriangular b (blockTriangular_toDual_of_isLo hb)]`. Conclude with `Finset.prod_ne_zero_iff.mp hb' l (Finset.mem_univ l)`.
-/
theorem diag_ne_zero_of_posDef_mul_conjTranspose {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b)
    (hx : (b * bᴴ).PosDef) (l : Fin n) : b l l ≠ 0 := by
  classical
  have hdet : (b * bᴴ).det ≠ 0 := hx.det_pos.ne'
  have hb' : b.det ≠ 0 := fun h => hdet (by rw [Matrix.det_mul, h, zero_mul])
  rw [Matrix.det_of_isLowerTriangular b (blockTriangular_toDual_of_isLo hb)] at hb'
  exact Finset.prod_ne_zero_iff.mp hb' l (Finset.mem_univ l)

/- English proof (translation)
Establish `hup : IsUp bᴴ` using `fun i j hji => by`. Simplify using `[Matrix.conjTranspose_apply, hb j i hji]`. Establish `h` using `hT n lam b 1 bᴴ hb hup (fun l => ⟨hd l, by simpa [Matrix.conjTranspose_apply] using hd l⟩) (one_mem_Omega_leadMinor n)`. Rewrite `h` using `[Matrix.mul_one]`. Use `⟨h.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h.2, Phi_at_one, mul_one, Complex.ofReal_prod]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_zpow, ← zpow_natCast, ← _root_.zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma phi_mul_conjTranspose_of_isLo (hT : PhiTri) {n : ℕ} (lam : Fin n → ℝ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) (hd : ∀ l, b l l ≠ 0) :
    b * bᴴ ∈ Omega n ∧ Phi lam (b * bᴴ) = ((∏ l, ‖b l l‖ ^ (-(2 * muInt lam l)) : ℝ) : ℂ) := by
  have hup : IsUp bᴴ := fun i j hji => by
    simp [Matrix.conjTranspose_apply, hb j i hji]
  have h := hT n lam b 1 bᴴ hb hup
    (fun l => ⟨hd l, by simpa [Matrix.conjTranspose_apply] using hd l⟩) (one_mem_Omega_leadMinor n)
  rw [Matrix.mul_one] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Phi_at_one, mul_one, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_zpow,
    ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `n lam x hx`. Take `⟨b, hb, rfl⟩` from `exists_isLo_mul_conjTranspose hx`. Establish `hd` using `fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb hx l`. Take `⟨hΩ, hΦ⟩` from `phi_mul_conjTranspose_of_isLo hT lam hb hd`. Use `⟨hΩ, ?_, ⟨b, hb, rfl⟩, fun b' hb' hx' => ?_⟩` and prove the remaining obligations.

Rewrite using `[hΦ, Complex.zero_lt_real]`. Conclude with `Finset.prod_pos fun l _ => zpow_pos (norm_pos_iff.mpr (hd l)) _`. Establish `hx2 : (b' * b'ᴴ).PosDef` using `hx' ▸ hx`. Rewrite using `[hx']`. Conclude with `(phi_mul_conjTranspose_of_isLo hT lam hb' (fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb' hx2 l)).2`.
-/
theorem phiPos_of_phiTri (hT : PhiTri) : PhiPos := by
  intro n lam x hx
  obtain ⟨b, hb, rfl⟩ := exists_isLo_mul_conjTranspose hx
  have hd := fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb hx l
  obtain ⟨hΩ, hΦ⟩ := phi_mul_conjTranspose_of_isLo hT lam hb hd
  refine ⟨hΩ, ?_, ⟨b, hb, rfl⟩, fun b' hb' hx' => ?_⟩
  · rw [hΦ, Complex.zero_lt_real]
    exact Finset.prod_pos fun l _ => zpow_pos (norm_pos_iff.mpr (hd l)) _
  · have hx2 : (b' * b'ᴴ).PosDef := hx' ▸ hx
    rw [hx']
    exact (phi_mul_conjTranspose_of_isLo hT lam hb'
      (fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb' hx2 l)).2

/- English proof (translation)
The claim follows from `phiPos_of_phiTri GlobalTheory.PhiTriangular.phiTri`.
-/
theorem phiPos : PhiPos := phiPos_of_phiTri GlobalTheory.PhiTriangular.phiTri

end GlobalTheory.Dec
