import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplGramMem

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma det_map_cast {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by
  have h := SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))
  simpa using h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma gram_diag {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by
  unfold symplGram qf intVec
  rw [Matrix.mul_mul_apply]
  rfl

end PSymplGramMem

open PSymplGramMem in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem SymplGramMem.proof : SymplGramMem.Statement := by
  intro n P G hP hG hGpd
  set P' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := P.map (Int.cast : ℤ → ℝ) with hP'
  have hP'mem : P' ∈ symplecticGroup (Fin n) ℝ := SymplecticGroup.map_mem hP (Int.castRingHom ℝ)
  refine ⟨?_, ?_, ?_, fun x => gram_diag P G x⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hP'mem hG) (SymplecticGroup.transpose_mem hP'mem)
  · have hdet : IsUnit P'.det := by rw [det_map_cast hP]; exact isUnit_one
    have hinj : Function.Injective P'.vecMul :=
      vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
    have h := hGpd.mul_mul_conjTranspose_same hinj
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  · intro Q
    unfold symplGram
    have hmap : (Q * P).map (Int.cast : ℤ → ℝ) = Q.map (Int.cast : ℤ → ℝ) * P.map (Int.cast : ℤ → ℝ) :=
      Matrix.map_mul (f := Int.castRingHom ℝ)
    rw [hmap, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
