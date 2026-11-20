import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {n r t : ℕ}

/- English proof (translation)
Simplify using `only [PositivityTheory.Rg.Rsw.bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem block_mul₂ {R : Type} [CommRing R] (hn : r + t = n) (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' = bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [PositivityTheory.Rg.Rsw.bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Unfold `PositivityTheory.GramSchwartzFunctions.EC.cT`. Rewrite using `[block_map]`. Simplify using `only [PositivityTheory.Rg.Rsw.bl, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]`.
-/
theorem cT_bl {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) (a : Matrix (Fin r) (Fin r) K) (b : Matrix (Fin r) (Fin t) K)
    (c : Matrix (Fin t) (Fin r) K) (d : Matrix (Fin t) (Fin t) K) :
    cT σ (bl hn a b c d) = bl hn (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  unfold PositivityTheory.GramSchwartzFunctions.EC.cT
  rw [block_map]
  simp only [PositivityTheory.Rg.Rsw.bl, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

/- English proof (translation)
Simplify using `[cT]`.
-/
theorem cT_zero {K : Type} [Field K] (σ : K →+* K) {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  simp [cT]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[block_mul₂]`. Simplify using the standard rewrite rules. Simplify using `only [cT_bl, cT_one, cT_zero]`.
-/
theorem first_block_hermitian_idempotent {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0 * bl hn 1 0 0 0 = bl hn 1 0 0 0 ∧
      cT σ (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0) = bl hn 1 0 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [block_mul₂]
    simp
  · simp only [cT_bl, cT_one, cT_zero]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[block_mul₂]`. Simplify using the standard rewrite rules. Simplify using `only [cT_bl, cT_one, cT_zero]`.
-/
theorem second_block_hermitian_idempotent {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1 * bl hn 0 0 0 1 = bl hn 0 0 0 1 ∧
      cT σ (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1) = bl hn 0 0 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [block_mul₂]
    simp
  · simp only [cT_bl, cT_one, cT_zero]

/- English proof (translation)
Rewrite using `[Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero σ) (map_one σ)]`.
-/
theorem Pm_map {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : (Pm K hn).map σ = Pm K hn := by
  rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero σ) (map_one σ)]

/- English proof (translation)
Rewrite using `[cT, Pm_map]`.
-/
theorem cT_Pm {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : cT σ (Pm K hn) = (Pm K hn)ᵀ := by
  rw [cT, Pm_map]

/- English proof (translation)
Rewrite using `[cT, Matrix.transpose_map, Pm_map, Matrix.transpose_transpose]`.
-/
theorem cT_PmT {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : cT σ (Pm K hn)ᵀ = Pm K hn := by
  rw [cT, Matrix.transpose_map, Pm_map, Matrix.transpose_transpose]

/- English proof (translation)
Establish `h0 : (PositivityTheory.GramSchwartzFunctions.EC.extB (n` using `n) (0 : Matrix (Fin p) (Fin p) K)) = 0 := by`. Use extensionality with `i j`. Simplify using `[PositivityTheory.GramSchwartzFunctions.EC.extB]`. Simplify using `only [PositivityTheory.GramSchwartzFunctions.EC.repMat, h0, PositivityTheory.GramSchwartzFunctions.EC.nB, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one, Matrix.mul_one]`.
-/
theorem repMat_zero {K : Type} [Field K] (σ : K →+* K) {p : ℕ} (a : Matrix (Fin n) (Fin n) K) :
    repMat σ (0 : Matrix (Fin p) (Fin p) K) a = wr K n p * mA σ a := by
  have h0 : (PositivityTheory.GramSchwartzFunctions.EC.extB (n := n) (0 : Matrix (Fin p) (Fin p) K)) = 0 := by
    ext i j
    simp [PositivityTheory.GramSchwartzFunctions.EC.extB]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.repMat, h0, PositivityTheory.GramSchwartzFunctions.EC.nB, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one, Matrix.mul_one]

/- English proof (translation)
Simplify using `only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_one, inv_one, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]`.
-/
theorem mA_one {K : Type} [Field K] (σ : K →+* K) : mA σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_one, inv_one, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]

/- English proof (translation)
Simplify using `only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_Pm, Matrix.inv_eq_left_inv (Pm_mul_alt (K := K) hn)]`.
-/
theorem mA_Pm {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : mA σ (Pm K hn) = blk4 (Pm K hn) 0 0 (Pm K hn) := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_Pm, Matrix.inv_eq_left_inv (Pm_mul_alt (K := K) hn)]

/- English proof (translation)
Establish `hc` using `eId_conj (K := K) hn`. Establish `h1 : (Pm K hn)ᵀ * (1 - PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = 1 - bl hn 0 0 0 1`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, T_mul_Pm, hc]`. Establish `h2 : (Pm K hn)ᵀ * (-PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = -bl hn 0 0 0 1`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hc]`.

Rewrite using `[repMat_zero, mA_Pm, ← Matrix.mul_assoc]`. Simplify using `only [PositivityTheory.GramSchwartzFunctions.EC.wr, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]`. Rewrite using `[h1, h2, hc]`. Both sides reduce to the same expression.
-/
theorem key3 {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * repMat σ (0 : Matrix (Fin t) (Fin t) K) (Pm K hn) = wE (bl hn 0 0 0 1) := by
  have hc := eId_conj (K := K) hn
  have h1 : (Pm K hn)ᵀ * (1 - PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = 1 - bl hn 0 0 0 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, T_mul_Pm, hc]
  have h2 : (Pm K hn)ᵀ * (-PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = -bl hn 0 0 0 1 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hc]
  rw [repMat_zero, mA_Pm, ← Matrix.mul_assoc]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.wr, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h1, h2, hc]
  rfl

/- English proof (translation)
Establish `hinv : blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * blk4 (Pm K hn) 0 0 (Pm K hn) = 1`. Rewrite using `[GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]`. Simplify using `only [T_mul_Pm, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]`. Use `⟨Matrix.isUnit_det_of_right_inverse hinv, ?_⟩` and prove the remaining obligations. Unfold `PositivityTheory.GramSchwartzFunctions.EC.IsUnitary PositivityTheory.GramSchwartzFunctions.EC.Jm`.

Rewrite using `[cT_blk4, cT_PmT, cT_zero]`. Simplify using `only [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, Pm_mul_alt, Matrix.one_mul, neg_zero]`.
-/
theorem gQ_unit {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ) := by
  have hinv : blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * blk4 (Pm K hn) 0 0 (Pm K hn) = 1 := by
    rw [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [T_mul_Pm, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  refine ⟨Matrix.isUnit_det_of_right_inverse hinv, ?_⟩
  unfold PositivityTheory.GramSchwartzFunctions.EC.IsUnitary PositivityTheory.GramSchwartzFunctions.EC.Jm
  rw [cT_blk4, cT_PmT, cT_zero]
  simp only [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, Pm_mul_alt, Matrix.one_mul, neg_zero]

/- English proof (translation)
Establish `h : PositivityTheory.GramSchwartzFunctions.EC.wr K n r = wE (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0)`. Rewrite using `[← eId_eq hn]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `wE_unit σ _ (first_block_hermitian_idempotent σ hn).1 (first_block_hermitian_idempotent σ hn).2`.
-/
theorem wr_unit {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (wr K n r).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wr K n r) := by
  have h : PositivityTheory.GramSchwartzFunctions.EC.wr K n r = wE (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0) := by
    rw [← eId_eq hn]
    rfl
  rw [h]
  exact wE_unit σ _ (first_block_hermitian_idempotent σ hn).1 (first_block_hermitian_idempotent σ hn).2

/- English proof (translation)
The claim follows from `wE_unit σ _ (second_block_hermitian_idempotent σ hn).1 (second_block_hermitian_idempotent σ hn).2`.
-/
theorem second_block_weyl_unitary {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (wE (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1)).det ∧
      IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wE (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1)) :=
  wE_unit σ _ (second_block_hermitian_idempotent σ hn).1 (second_block_hermitian_idempotent σ hn).2

end PositivityTheory.Rg.Rsw.L.LPartFT
