import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC.LeftCell

variable {D : D7} {p : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]`. Simplify using `only [blk4, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]`.
-/
theorem upper_triangular_block_mul_lower_rows (a b d : Mx D p p) (N : Mx D (p + p) (p + p)) (k : Fin p → Fin (p + p)) :
    (blk4 a b 0 d * N).submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k =
      d * N.submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [blk4, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [lowD, h, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]`.
-/
theorem lowerDiagonal_of_upper_triangular_block {a b d : Mx D p p} {q : G D p} (h : mat q = blk4 a b 0 d) : lowD q = d := by
  ext i j
  simp only [lowD, h, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

/- English proof (translation)
Take `⟨b, d, hm⟩` from `GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq`. Establish `hd` using `lowerDiagonal_of_upper_triangular_block hm`. Rewrite using `[hd]`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `(mat (q * g)).submatrix _ _ = _`.

Rewrite using `[GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]`. Conclude with `upper_triangular_block_mul_lower_rows _ _ _ _ _`. Express the relevant statement in the definitionally equal form `(mat (q * g)).submatrix _ _ = _`. Rewrite using `[GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]`. Conclude with `upper_triangular_block_mul_lower_rows _ _ _ _ _`.
-/
theorem low_mul {q : G D p} (hq : q ∈ P D p) (g : G D p) :
    lowC (q * g) = lowD q * lowC g ∧ lowD (q * g) = lowD q * lowD g := by
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  have hd := lowerDiagonal_of_upper_triangular_block hm
  rw [hd]
  constructor
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[lowD, GlobalTheory.StdUnn.LeftInvSect.mat_one, Matrix.one_apply]`.
-/
theorem lowD_one : lowD (1 : G D p) = 1 := by
  ext i j
  simp [lowD, GlobalTheory.StdUnn.LeftInvSect.mat_one, Matrix.one_apply]

/- English proof (translation)
Establish `h` using `(low_mul ((P D p).inv_mem hq) q).2`. Rewrite `h` using `[inv_mul_cancel, lowD_one]`. Conclude with `h.symm`.
-/
theorem lowD_inv_mul {q : G D p} (hq : q ∈ P D p) : lowD q⁻¹ * lowD q = 1 := by
  have h := (low_mul ((P D p).inv_mem hq) q).2
  rw [inv_mul_cancel, lowD_one] at h
  exact h.symm

/- English proof (translation)
Take `⟨⟨y, hy⟩, hx⟩` from `h`. Take `⟨hC, hD⟩` from `low_mul hq g`. Use `⟨⟨mm y (lowD q⁻¹), ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(y * lowD q⁻¹) * lowC (q * g) = _`. Express the relevant statement in the definitionally equal form `y * lowC g = _ at hy`.

Rewrite using `[hC, Matrix.mul_assoc, ← Matrix.mul_assoc (lowD q⁻¹), lowD_inv_mul hq, Matrix.one_mul, hy]`. Express the relevant statement in the definitionally equal form `lowC (q * g) * x.1.1 = _`. Express the relevant statement in the definitionally equal form `lowC g * x.1.1 = _ at hx`. Rewrite using `[hC, hD, Matrix.mul_assoc, hx, Matrix.mul_smul]`.
-/
theorem isB_mul {e : AE D} {q g : G D p} (hq : q ∈ P D p) {x : hermS D p e} (h : IsB e g x) :
    IsB e (q * g) x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨hC, hD⟩ := low_mul hq g
  refine ⟨⟨mm y (lowD q⁻¹), ?_⟩, ?_⟩
  · change (y * lowD q⁻¹) * lowC (q * g) = _
    change y * lowC g = _ at hy
    rw [hC, Matrix.mul_assoc, ← Matrix.mul_assoc (lowD q⁻¹), lowD_inv_mul hq, Matrix.one_mul, hy]
  · change lowC (q * g) * x.1.1 = _
    change lowC g * x.1.1 = _ at hx
    rw [hC, hD, Matrix.mul_assoc, hx, Matrix.mul_smul]

/- English proof (translation)
Introduce `D p e q g hq x`. Use `⟨fun h => ?_, isB_mul hq⟩` and prove the remaining obligations. Establish `h'` using `isB_mul ((P D p).inv_mem hq) h`. Rewrite `h'` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis.
-/
theorem isB_left : ∀ {D : D7} {p : ℕ} {e : AE D} {q g : G D p} (hq : q ∈ P D p) (x : hermS D p e),
    IsB e (q * g) x ↔ IsB e g x := by
  intro D p e q g hq x
  refine ⟨fun h => ?_, isB_mul hq⟩
  have h' := isB_mul ((P D p).inv_mem hq) h
  rwa [inv_mul_cancel_left] at h'

end GlobalTheory.CompanionTheory.MuC.LeftCell
