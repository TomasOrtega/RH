import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

def leftMul (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Matrix (Fin a) (Fin b) R ≃ₗ[R] Matrix (Fin a) (Fin b) R where
  toFun x := Jiᵀ * x
  invFun y := Jᵀ * y
  map_add' := Matrix.mul_add _
  map_smul' c x := Matrix.mul_smul _ c x
  left_inv x := by
    change Jᵀ * (Jiᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    change Jiᵀ * (Jᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, mul_eq_one_comm.1 h1, Matrix.transpose_one, Matrix.one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gen_supp (f : R) (g : Matrix (Fin a) (Fin a) R) :
    (∀ i j, f * (g - 1) i j = (g - 1) i j) ↔ (1 - f) • g = (1 - f) • (1 : Matrix (Fin a) (Fin a) R) := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> linear_combination -h

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem gen_cont [TopologicalSpace R] [IsTopologicalRing R] (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Continuous (leftMul (b := b) J Ji h1) ∧ Continuous (leftMul (b := b) J Ji h1).symm :=
  ⟨continuous_const.matrix_mul continuous_id, continuous_const.matrix_mul continuous_id⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) : SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (e + HeisenbergWeilMatrices.cj D e) g :=
  gen_supp _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem suppAt_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (V : HSp D)
    (g : GA D V) : SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (HeisenbergWeilMatrices.idemFin D v) g := by
  rw [suppAt_iff', he.sum]

end GlobalTheory.DualPairCompare

end
