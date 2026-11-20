import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)

def mulMat {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' ((j : A.L →ₗ[E] (Fin r → E)) ∘ₗ LinearMap.mulLeft E y ∘ₗ (j.symm : (Fin r → E) →ₗ[E] A.L))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mulMat_mulVec {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) (v : Fin r → E) :
    A.mulMat j y *ᵥ v = j (y * j.symm v) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mulMat_mulVec_apply {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y z : A.L) :
    A.mulMat j y *ᵥ j z = j (y * z) := by
  simp [mulMat_mulVec]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem mulMat_mul {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y y' : A.L) :
    A.mulMat j (y * y') = A.mulMat j y * A.mulMat j y' := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_assoc]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem mulMat_one {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) : A.mulMat j 1 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [mulMat_mulVec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem mulMat_mem_unitaryGroup {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j)
    (t : unitary A.L) : A.mulMat j t ∈ Matrix.unitaryGroup (Fin r) E := by
  rw [Matrix.mem_unitaryGroup_iff']
  set N := star (A.mulMat j t) * A.mulMat j t
  have key : ∀ v w : Fin r → E, star v ⬝ᵥ (N *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    obtain ⟨a, rfl⟩ := j.surjective v
    obtain ⟨b, rfl⟩ := j.surjective w
    have h1 : star (j a) ⬝ᵥ (N *ᵥ j b) = star (A.mulMat j t *ᵥ j a) ⬝ᵥ (A.mulMat j t *ᵥ j b) := by
      simp only [N, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    rw [h1, mulMat_mulVec_apply, mulMat_mulVec_apply, hx, hx]
    congr 1
    have ht : star (t : A.L) * t = 1 := Unitary.star_mul_self_of_mem t.2
    calc algebraMap A.K A.L x * star ((t : A.L) * a) * ((t : A.L) * b)
        = algebraMap A.K A.L x * star a * b * (star (t : A.L) * t) := by rw [star_mul]; ring
      _ = _ := by rw [ht, mul_one]
  have hw : ∀ w, N *ᵥ w = w := by
    intro w
    funext i
    have := key (Pi.single i 1) w
    simpa [single_dotProduct] using this
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simp [hw]

def uHom {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) :
    unitary A.L →* Matrix.unitaryGroup (Fin r) E where
  toFun t := ⟨A.mulMat j t, A.mulMat_mem_unitaryGroup hx t⟩
  map_one' := by ext1; simp [mulMat_one]
  map_mul' t t' := by ext1; simp [mulMat_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uHom_apply {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (t : unitary A.L) :
    (A.uHom hx t : Matrix (Fin r) (Fin r) E) = A.mulMat j t := rfl

def descFn {r : ℕ} (M : GlobalTheory.JR.Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E))
    (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ) (f : Hn r F E → ℂ) (y : A.L) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g (Ax, j y, lam)) * (α g : ℂ) ∂M.μU

end GlobalTheory.JR.Et
