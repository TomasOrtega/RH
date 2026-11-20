import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplGramMem

/- English proof (translation)
Establish `h` using `SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))`. Simplify using `using h`.
-/
lemma det_map_cast {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by
  have h := SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))
  simpa using h

/- English proof (translation)
Unfold `symplGram qf intVec`. Rewrite using `[Matrix.mul_mul_apply]`. Both sides reduce to the same expression.
-/
lemma gram_diag {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by
  unfold symplGram qf intVec
  rw [Matrix.mul_mul_apply]
  rfl

end PSymplGramMem

open PSymplGramMem in

/- English proof (translation)
Introduce `n P G hP hG hGpd`. Use `set P' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := P.map (Int.cast : ℤ → ℝ) with hP'`. Establish `hP'mem : P' ∈ symplecticGroup (Fin n) ℝ` using `SymplecticGroup.map_mem hP (Int.castRingHom ℝ)`. Use `⟨?_, ?_, ?_, fun x => gram_diag P G x⟩` and prove the remaining obligations. Conclude with `Submonoid.mul_mem _ (Submonoid.mul_mem _ hP'mem hG) (SymplecticGroup.transpose_mem hP'mem)`.

Establish `hdet : IsUnit P'.det` using `by rw [det_map_cast hP]; exact isUnit_one`. Establish `hinj : Function.Injective P'.vecMul` using `vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)`. Establish `h` using `hGpd.mul_mul_conjTranspose_same hinj`. Rewrite `h` using `[conjTranspose_eq_transpose_of_trivial]`. Then use the resulting hypothesis. Introduce `Q`.

Unfold `symplGram`. Establish `hmap : (Q * P).map (Int.cast : ℤ → ℝ) = Q.map (Int.cast : ℤ → ℝ) * P.map (Int.cast : ℤ → ℝ)` using `Matrix.map_mul (f := Int.castRingHom ℝ)`. Rewrite using `[hmap, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
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
