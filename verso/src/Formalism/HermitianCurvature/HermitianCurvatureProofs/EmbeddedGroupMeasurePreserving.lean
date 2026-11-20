import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

/- English proof (translation)
Introduce `k p ρ Z γ y₁ y₂`. Simplify using `only [U.mMap, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]`.
-/
theorem embedding_map_embedded_group : MMapEmbG := by
  intro k p ρ Z γ y₁ y₂
  simp only [U.mMap, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `k p ρ y q`. Simplify using `only [U.muP, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem embedded_group_measure_preserving : EmbGMuP := by
  intro k p ρ y q
  simp only [U.muP, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
private theorem wMat_mul_self_eq_one (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  split_ifs <;> simp_all

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, wMat_mul_self_eq_one, Matrix.one_mul]`.
-/
private theorem wMat_mul_wMat_mul' (d : ℕ) {m : Type*} (X : Matrix (Fin d) m ℂ) : G.wMat d * (G.wMat d * X) = X := by
  rw [← Matrix.mul_assoc, wMat_mul_self_eq_one, Matrix.one_mul]

/- English proof (translation)
Introduce `k p ρ l Z u γ hl`. Simplify using `only [U.mMap, U.muP, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_nonsing_inv l h …`.
-/
theorem embedding_map_lower_unipotent : MMapLZU := by
  intro k p ρ l Z u γ hl
  simp only [U.mMap, U.muP, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_nonsing_inv l hl,
    Matrix.mul_assoc, wMat_mul_wMat_mul']

/- English proof (translation)
Introduce `k p ρ y x hy`. Establish `h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1` using `rfl`. Establish `h2 : (rcAct y x).2 = x.2` using `rfl`. Establish `h3 : yᴴ * (Hpk k ρ * y) = Hpk k ρ` using `by rw [← Matrix.mul_assoc, hy]`. Establish `h4 : ∀ M : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ, yᴴ * (Hpk k ρ * (y * M)) = Hpk k ρ * M`.

Introduce `M`. Rewrite using `[← Matrix.mul_assoc (Hpk k ρ), ← Matrix.mul_assoc, h3]`. Simplify using `only [U.Rn, U.embG, Ux5.block3_mul_blocks, h1, h2, Matrix.conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h …`.
-/
theorem embedded_group_right_action : EmbGRn := by
  intro k p ρ y x hy
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have h2 : (rcAct y x).2 = x.2 := rfl
  have h3 : yᴴ * (Hpk k ρ * y) = Hpk k ρ := by rw [← Matrix.mul_assoc, hy]
  have h4 : ∀ M : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ, yᴴ * (Hpk k ρ * (y * M)) = Hpk k ρ * M := by
    intro M
    rw [← Matrix.mul_assoc (Hpk k ρ), ← Matrix.mul_assoc, h3]
  simp only [U.Rn, U.embG, Ux5.block3_mul_blocks, h1, h2, Matrix.conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3, h4,
    neg_zero, smul_zero]

/- English proof (translation)
Use extensionality with `a c`. Establish `h : σ (σ⁻¹ a) = a` using `σ.apply_symm_apply a`. Simplify using `only [U.wP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, h]`.
-/
private theorem wP_inv_mul_wP_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ⁻¹ * U.wP σ = 1 := by
  ext a c
  have h : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
  simp only [U.wP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h]

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_left_inverse (wP_inv_mul_wP_eq_one σ)`.
-/
private theorem isUnit_det_wP {p : ℕ} (σ : Equiv.Perm (Fin p)) : IsUnit (U.wP σ).det :=
  Matrix.isUnit_det_of_left_inverse (wP_inv_mul_wP_eq_one σ)

/- English proof (translation)
Establish `hinv : (U.wP σ)⁻¹ = U.wP σ⁻¹` using `Matrix.inv_eq_left_inv (wP_inv_mul_wP_eq_one σ)`. Apply the tactic sequence `have hentry : ∀ a b, lhOf σ v a b = U.lowW σ v (σ a) (σ b) := by`. Introduce `a b`. Rewrite using `[lhOf, hinv]`. Simplify using `only [Matrix.mul_apply, U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.Perm.inv_eq_iff_eq, Finset.sum_ite_eq']`.

Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, hentry]`. Simplify using `[U.lowW]`. Simplify using `only [Matrix.transpose_apply, hentry]`. Establish `h1 : σ j ≠ σ i` using `fun h => (ne_of_lt hij) (σ.injective h)`.

Establish `h2 : ¬ (i < j)` using `not_lt.mpr hij.le`. Simplify using `[U.lowW, Matrix.one_apply, h1, h2]`.
-/
theorem lh_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : G.IsLowerUni (lhOf σ v) := by
  have hinv : (U.wP σ)⁻¹ = U.wP σ⁻¹ := Matrix.inv_eq_left_inv (wP_inv_mul_wP_eq_one σ)
  have hentry : ∀ a b, lhOf σ v a b = U.lowW σ v (σ a) (σ b) := by
    intro a b
    rw [lhOf, hinv]
    simp only [Matrix.mul_apply, U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.Perm.inv_eq_iff_eq, Finset.sum_ite_eq']
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Matrix.transpose_apply, hentry]
    simp [U.lowW]
  · simp only [Matrix.transpose_apply, hentry]
    have h1 : σ j ≠ σ i := fun h => (ne_of_lt hij) (σ.injective h)
    have h2 : ¬ (i < j) := not_lt.mpr hij.le
    simp [U.lowW, Matrix.one_apply, h1, h2]

/- English proof (translation)
Introduce `p σ d v u`. Use `⟨?_, lh_lower σ v⟩` and prove the remaining obligations. Simplify using `only [U.headH, lhOf, U.hMat, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), Matrix.nonsing_inv_mul _ (isUnit_det_wP σ), Matrix.one_mul]`.
-/
theorem head_hermitian_eq : HeadHEq := by
  intro p σ d v u
  refine ⟨?_, lh_lower σ v⟩
  simp only [U.headH, lhOf, U.hMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), Matrix.nonsing_inv_mul _ (isUnit_det_wP σ), Matrix.one_mul]

/- English proof (translation)
Use extensionality with `i j`. Establish `hi : finSumFinEquiv.symm i = Sum.inl i`. Rewrite using `[Equiv.symm_apply_eq]`. Apply the tactic sequence `exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])`. Establish `hj : finSumFinEquiv.symm j = Sum.inl j`.

Rewrite using `[Equiv.symm_apply_eq]`. Apply the tactic sequence `exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])`. Simplify using `[U.blk2, Matrix.reindex_apply, hi, hj]`.
-/
private theorem blk2_fin_zero_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 0) ℂ)
    (C : Matrix (Fin 0) (Fin p) ℂ) (D : Matrix (Fin 0) (Fin 0) ℂ) : U.blk2 A B' C D = A := by
  ext i j
  have hi : finSumFinEquiv.symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  have hj : finSumFinEquiv.symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  simp [U.blk2, Matrix.reindex_apply, hi, hj]

/- English proof (translation)
Introduce `p σ d η Z`. Simplify using `only [U.ZjH, U.Zj, blk2_fin_zero_eq, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem lower_corner_hermitian_zero : ZjHZero := by
  intro p σ d η Z
  simp only [U.ZjH, U.Zj, blk2_fin_zero_eq, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `hL : (U.lowW σ v).det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular _ ?_]`. Simplify using `[U.lowW]`. Introduce `i j hij`. Establish `h1 : i < j` using `OrderDual.toDual_lt_toDual.mp hij`.

Establish `h2 : ¬ j < i` using `not_lt.mpr h1.le`. Simplify using `[U.lowW, Matrix.one_apply, ne_of_lt h1, h2]`. Simplify using `only [lhOf, Matrix.det_mul, hL, mul_one]`. Conclude with `(isUnit_det_wP σ).mul (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_wP σ))`.
-/
theorem lh_unit {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : IsUnit (lhOf σ v).det := by
  have hL : (U.lowW σ v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ?_]
    · simp [U.lowW]
    · intro i j hij
      have h1 : i < j := OrderDual.toDual_lt_toDual.mp hij
      have h2 : ¬ j < i := not_lt.mpr h1.le
      simp [U.lowW, Matrix.one_apply, ne_of_lt h1, h2]
  simp only [lhOf, Matrix.det_mul, hL, mul_one]
  exact (isUnit_det_wP σ).mul (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_wP σ))

/- English proof (translation)
Introduce `k p ρ σ d ξ Z h ν h' ν' g hh hν hh'`. Establish `hZ : U.ZjH σ d ξ.2 Z = lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2`. Rewrite using `[lower_corner_hermitian_zero p σ d ξ.2 Z]`. Conclude with `(head_hermitian_eq p σ d ξ.2.2.1 ξ.2.2.2).1`. Establish `hγ : h⁻¹ * ν⁻¹ * g * ν' * h' = (h⁻¹ * ν⁻¹) * g * (ν' * h')`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hE : U.embG k p ρ (ν' * h') = U.embG k p ρ ν' * U.embG k p ρ h'`. Simplify using `only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]`. Simplify using `only [U.gaXi]`. Rewrite using `[PBM.rn_inv, hZ]`.

Use `show U.Rn k p ρ (-ξ.1.1) * U.mMap k p ρ (lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2) (h⁻¹ * ν⁻¹ * g * ν' * h') * U.Rn k p ρ ξ.1.2 = _`. Rewrite using `[embedding_map_lower_unipotent k p ρ _ _ _ _ (lh_unit σ ξ.2.2.1), hγ, embedding_map_embedded_group, hE]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (U.embG k p ρ h') (U.muP k p ρ (G.upper ξ.2.2.2)), embedded_group_measure_preserving k p ρ h' (G.upper ξ.2.2.2), Matrix.mul_assoc, embedded_group_right_action k p ρ h' ξ.1.2 hh']`.
-/
theorem gamma_xi_split : GaXiSplit := by
  intro k p ρ σ d ξ Z h ν h' ν' g hh hν hh'
  have hZ : U.ZjH σ d ξ.2 Z = lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2 := by
    rw [lower_corner_hermitian_zero p σ d ξ.2 Z]
    exact (head_hermitian_eq p σ d ξ.2.2.1 ξ.2.2.2).1
  have hγ : h⁻¹ * ν⁻¹ * g * ν' * h' = (h⁻¹ * ν⁻¹) * g * (ν' * h') := by
    simp only [Matrix.mul_assoc]
  have hE : U.embG k p ρ (ν' * h') = U.embG k p ρ ν' * U.embG k p ρ h' := by
    simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  simp only [U.gaXi]
  rw [PBM.rn_inv, hZ]
  show U.Rn k p ρ (-ξ.1.1) * U.mMap k p ρ (lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2) (h⁻¹ * ν⁻¹ * g * ν' * h') *
      U.Rn k p ρ ξ.1.2 = _
  rw [embedding_map_lower_unipotent k p ρ _ _ _ _ (lh_unit σ ξ.2.2.1), hγ, embedding_map_embedded_group, hE]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.embG k p ρ h') (U.muP k p ρ (G.upper ξ.2.2.2)),
    embedded_group_measure_preserving k p ρ h' (G.upper ξ.2.2.2), Matrix.mul_assoc, embedded_group_right_action k p ρ h' ξ.1.2 hh']

/- English proof (translation)
Rewrite `hy`, the goal using `[WeylGroupFacts.nset_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (U.embG k p ρ y)ᴴ * Hpk k (p + ρ) * U.embG k p ρ y = Hpk k (p + ρ)`. Establish `hy1 : yᴴ * Hpk k ρ * y = Hpk k ρ` using `hy.1`. Rewrite using `[Formalism.FourierDecayAlt.P.hermitian_group_blocks k p ρ, U.embG, Ux3.block3_conjTranspose, Ux3.block3_mul, Ux3.block3_mul]`.

Apply the tactic sequence `congr 1 <;> simp [hy1]`. Introduce `i c hc hi`. Take `⟨x, rfl⟩` from `(U.eB k p ρ).surjective i`. Take `⟨w, rfl⟩` from `(U.eB k p ρ).surjective c`. Rewrite using `[U.embG, Ux3.block3_apply]`.

Simplify using `only [(U.eB k p ρ).apply_eq_iff_eq]`. Apply the tactic sequence `rcases x with ((x | x) | x) <;> rcases w with ((w | w) | w) <;>`. Apply the tactic sequence `simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc hi <;>`. Use `first`. Consider the case `(simp [Matrix.one_apply]; done)`.

Consider the case `(exfalso; have := x.isLt; have := w.isLt; omega)`. Consider the case `skip`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]`. Conclude with `hy.2 x w (by omega) (by omega)`.
-/
theorem embG_nset {k p ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ QuantumDeterminants.Nset k ρ) : U.embG k p ρ y ∈ QuantumDeterminants.Nset k (p + ρ) := by
  rw [WeylGroupFacts.nset_iff] at hy ⊢
  refine ⟨?_, ?_⟩
  · show (U.embG k p ρ y)ᴴ * Hpk k (p + ρ) * U.embG k p ρ y = Hpk k (p + ρ)
    have hy1 : yᴴ * Hpk k ρ * y = Hpk k ρ := hy.1
    rw [Formalism.FourierDecayAlt.P.hermitian_group_blocks k p ρ, U.embG, Ux3.block3_conjTranspose, Ux3.block3_mul, Ux3.block3_mul]
    congr 1 <;> simp [hy1]
  · intro i c hc hi
    obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
    obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective c
    rw [U.embG, Ux3.block3_apply]
    simp only [(U.eB k p ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases w with ((w | w) | w) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc hi <;>
      first
      | (simp [Matrix.one_apply]; done)
      | (exfalso; have := x.isLt; have := w.isLt; omega)
      | skip
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]
    exact hy.2 x w (by omega) (by omega)

/- English proof (translation)
Introduce `k p ρ z x l h ν hz hl hh hν`. Establish `hH` using `Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ`. Establish `hhu : IsUnit h.det` using `WeylGroupFacts.isUnit_of_uh hh.1`. Establish `hclN` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)`. Establish `hlH : G.IsUpperUni lᴴ`.

Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, show l i i = lᵀ i i from rfl, hl.1 i, star_one]`. Rewrite using `[Matrix.conjTranspose_apply, show l j i = lᵀ i j from rfl, hl.2 i j hij, star_zero]`. Establish `hlu : IsUnit (lᴴ).det` using `by rw [Formalism.FourierDecayAlt.P.G4.upperUni_det hlH]; exact isUnit_one`. Establish `hmu : U.muP k p ρ (lᴴ)⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ)`.

Rewrite using `[← Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hlu]`. Use `hclN.inv_mem _ (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ ⟨fun i j hij => hlH.2 i j hij, hlH.1⟩)` and prove the remaining obligations. Establish `hRn : U.Rn k p ρ (rcAct h x) ∈ QuantumDeterminants.Nset k (p + ρ)` using `(Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨rcAct h x, rfl⟩)`. Establish `hνN : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ)` using `embG_nset ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).inv_mem ν hν)`. Establish `hW : U.embG k p ρ h⁻¹ ∈ UWset k (p + ρ) (liftVec k p ρ z)`.

Rewrite using `[← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]`. Conclude with `Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW p ρ z _ (WeylGroupFacts.uw_inv hh)`. Use `⟨U.embG k p ρ h⁻¹, hW, U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ ν⁻¹, hclN.mul_mem _ (hclN.mul_mem _ hRn _ hmu) _ hνN, ?_⟩` and prove the remaining obligations. Establish `e1 : U.embG k p ρ h * U.Rn k p ρ x = U.Rn k p ρ (rcAct h x) * U.embG k p ρ h` using `embedded_group_right_action k p ρ h x hh.1`. Establish `e2 : U.embG k p ρ h⁻¹ * U.embG k p ρ h = 1`.

Rewrite using `[← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, Matrix.nonsing_inv_mul _ hhu, Formalism.FourierDecayAlt.P.PBM.embG_one]`. Establish `e3 : U.Rn k p ρ x = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.embG k p ρ h`. Rewrite using `[Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]`. Establish `e4 : U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹) = U.embG k p ρ ν⁻¹`. Rewrite using `[← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]`.

Establish `e5 : U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹ = U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ h` using `embedded_group_measure_preserving k p ρ h _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem left_factor_mem : LeftMem := by
  intro k p ρ z x l h ν hz hl hh hν
  have hH := Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ
  have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have hclN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)

  have hlH : G.IsUpperUni lᴴ := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_apply, show l i i = lᵀ i i from rfl, hl.1 i, star_one]
    · rw [Matrix.conjTranspose_apply, show l j i = lᵀ i j from rfl, hl.2 i j hij, star_zero]
  have hlu : IsUnit (lᴴ).det := by rw [Formalism.FourierDecayAlt.P.G4.upperUni_det hlH]; exact isUnit_one
  have hmu : U.muP k p ρ (lᴴ)⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) := by
    rw [← Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hlu]
    refine hclN.inv_mem _ (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ ⟨fun i j hij => hlH.2 i j hij, hlH.1⟩)
  have hRn : U.Rn k p ρ (rcAct h x) ∈ QuantumDeterminants.Nset k (p + ρ) :=
    (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨rcAct h x, rfl⟩)
  have hνN : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) :=
    embG_nset ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).inv_mem ν hν)
  have hW : U.embG k p ρ h⁻¹ ∈ UWset k (p + ρ) (liftVec k p ρ z) := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]; exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW p ρ z _ (WeylGroupFacts.uw_inv hh)
  refine ⟨U.embG k p ρ h⁻¹, hW, U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ ν⁻¹,
    hclN.mul_mem _ (hclN.mul_mem _ hRn _ hmu) _ hνN, ?_⟩
  have e1 : U.embG k p ρ h * U.Rn k p ρ x = U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := embedded_group_right_action k p ρ h x hh.1
  have e2 : U.embG k p ρ h⁻¹ * U.embG k p ρ h = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, Matrix.nonsing_inv_mul _ hhu, Formalism.FourierDecayAlt.P.PBM.embG_one]
  have e3 : U.Rn k p ρ x = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  have e4 : U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹) = U.embG k p ρ ν⁻¹ := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  have e5 : U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹ = U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ h := embedded_group_measure_preserving k p ρ h _
  calc U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)
      = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * (U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹) *
          U.embG k p ρ (h⁻¹ * ν⁻¹) := by rw [e3]; simp only [Matrix.mul_assoc]
    _ = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ *
          (U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹)) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e4]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
