import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype

noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open InnerProductSpace

/- English proof (translation)
Introduce `N X`. Set `f : Fin N → EuclideanSpace ℂ (Fin N)` to `fun j => (WithLp.equiv 2 _).symm (fun a => X a j)`. Establish `hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N)` using `finrank_euclideanSpace`. Set `b` to `gramSchmidtOrthonormalBasis hd f`. Set `k : Matrix (Fin N) (Fin N) ℂ` to `Matrix.of fun a j => b j a`.

Establish `hinner : ∀ i j, ∑ a, star (b i a) * (f j) a = inner ℂ (b i) (f j)`. Introduce `i j`. Simplify using `[PiLp.inner_apply, mul_comm]`. Establish `hinner' : ∀ i j, ∑ a, star (b i a) * b j a = inner ℂ (b i) (b j)`. Introduce `i j`.

Simplify using `[PiLp.inner_apply, mul_comm]`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Use extensionality with `i j`. Establish `ho` using `orthonormal_iff_ite.mp b.orthonormal i j`.

Simplify using `only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply, Matrix.one_apply]`. Rewrite using `[hinner', ho]`. Introduce `a j hja`. Use `gramSchmidtOrthonormalBasis_inv_triangular hd f hja` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply]`.

Rewrite using `[← this, ← hinner]`. Both sides reduce to the same expression.
-/
theorem quotient_rank : QR := by
  intro N X
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => (WithLp.equiv 2 _).symm (fun a => X a j)
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := finrank_euclideanSpace
  let b := gramSchmidtOrthonormalBasis hd f
  let k : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a j => b j a
  have hinner : ∀ i j, ∑ a, star (b i a) * (f j) a = inner ℂ (b i) (f j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  have hinner' : ∀ i j, ∑ a, star (b i a) * b j a = inner ℂ (b i) (b j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  refine ⟨k, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have ho := orthonormal_iff_ite.mp b.orthonormal i j
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply, Matrix.one_apply]
    rw [hinner', ho]
  · intro a j hja
    have := gramSchmidtOrthonormalBasis_inv_triangular hd f hja
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply]
    rw [← this, ← hinner]
    rfl

end PI.IsoInvMetricW
