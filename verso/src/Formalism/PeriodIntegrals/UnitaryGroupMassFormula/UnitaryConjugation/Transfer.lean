import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.TransferStep

noncomputable section

namespace PI.UConjT

open Matrix

/- English proof (translation)
Rewrite using `[EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]`. Rewrite using `[star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec, dotProduct_comm]`.
-/
lemma inner_toEuclideanLin_unitary {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (hg : gᴴ * g = 1)
    (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (Matrix.toEuclideanLin g x) (Matrix.toEuclideanLin g y) = inner ℂ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec,
    dotProduct_comm]

/- English proof (translation)
Introduce `hO n g hg`. Establish `hg2 : gᴴ * g = 1`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `mem_unitaryGroup_iff'.mp hg`. Take `⟨b, hbo, hbe, hbr⟩` from `hO (n + 1) (EuclideanSpace ℂ (Fin (n + 1))) finrank_euclideanSpace_fin (Matrix.toEuclideanLin g) (inner_toEuclideanLin_unitary g hg2) (EuclideanSpace.single (Fin.last n) 1)`.

Use `choose d hd using hbe`. Use `⟨Matrix.of fun i j => b j i, ?_, d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_unitaryGroup_iff']`. Use extensionality with `i j`. Establish `h1` using `orthonormal_iff_ite.mp hbo i j`.

Rewrite `h1` using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [star_eq_conjTranspose, mul_apply, conjTranspose_apply, of_apply, one_apply]`. Rewrite using `[← h1]`. Simplify using `[dotProduct, mul_comm]`. Use extensionality with `i j`.

Establish `h1` using `congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) => v i) (hd j)`. Simplify using `only [Matrix.toLpLin_apply, PiLp.smul_apply, smul_eq_mul] at h1`. Rewrite using `[mul_diagonal, mul_apply]`. Simplify using `only [of_apply]`. Simplify `h1` using `[mulVec, dotProduct, mul_comm]`.

Introduce `i`. Establish `h1` using `hbr i`. Rewrite `h1` using `[EuclideanSpace.inner_single_right]`. Simplify using `using h1`.
-/
theorem transferStep : TransferStep := by
  intro hO n g hg
  have hg2 : gᴴ * g = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hg
  obtain ⟨b, hbo, hbe, hbr⟩ := hO (n + 1) (EuclideanSpace ℂ (Fin (n + 1)))
    finrank_euclideanSpace_fin (Matrix.toEuclideanLin g) (inner_toEuclideanLin_unitary g hg2)
    (EuclideanSpace.single (Fin.last n) 1)
  choose d hd using hbe
  refine ⟨Matrix.of fun i j => b j i, ?_, d, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    ext i j
    have h1 := orthonormal_iff_ite.mp hbo i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
    simp only [star_eq_conjTranspose, mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [← h1]
    simp [dotProduct, mul_comm]
  · ext i j
    have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) => v i) (hd j)
    simp only [Matrix.toLpLin_apply, PiLp.smul_apply, smul_eq_mul] at h1
    rw [mul_diagonal, mul_apply]
    simp only [of_apply]
    simpa [mulVec, dotProduct, mul_comm] using h1
  · intro i
    have h1 := hbr i
    rw [EuclideanSpace.inner_single_right] at h1
    simpa using h1

end PI.UConjT
