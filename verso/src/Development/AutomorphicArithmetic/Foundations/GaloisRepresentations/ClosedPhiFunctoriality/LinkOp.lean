import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One

noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Introduce `R _ π s d d' W Z Zs W₁ Z₁ Zs₁ Pm R₀ h1 h2 hA hB i j`. Establish `hl : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) R) (A : Matrix (Fin n) (Fin p) R), (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (X * A) i j`. Introduce `m n p X A h i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.dvd_sum fun k _ => (h k j).mul_left _`.

Establish `hr : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R) (Y : Matrix (Fin n) (Fin p) R), (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (A * Y) i j`. Introduce `m n p A Y h i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.dvd_sum fun k _ => (h i k).mul_right _`. Establish `e1 : W * Zs * Pm * Z₁ * Zs₁ = s • (W * Zs * Pm)`.

Rewrite using `[Matrix.mul_assoc (W * Zs * Pm), h2, Matrix.mul_smul, Matrix.mul_one]`. Establish `e2 : W * Zs * Z * R₀ * Zs₁ = s • (W * R₀ * Zs₁)`. Rewrite using `[Matrix.mul_assoc W Zs Z, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul]`. Establish `key : s • (W * Zs) * Pm - Pm * s • (W₁ * Zs₁) = W * Zs * (Pm * Z₁ - Z * R₀) * Zs₁ - s • ((Pm * W₁ - W * R₀) * Zs₁)`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, smul_sub, Matrix.smul_mul, Matrix.mul_smul]`.

Rewrite using `[e1, e2]`. Normalize the expressions using the abelian group laws. Rewrite using `[key, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `dvd_sub (hr _ _ (hl _ _ hA) i j) ((hr _ _ hB i j).mul_left s)`.
-/
theorem linkOp_holds : LinkOp2 := by
  intro R _ π s d d' W Z Zs W₁ Z₁ Zs₁ Pm R₀ h1 h2 hA hB i j
  have hl : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) R) (A : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (X * A) i j := by
    intro m n p X A h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h k j).mul_left _
  have hr : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R) (Y : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (A * Y) i j := by
    intro m n p A Y h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h i k).mul_right _
  have e1 : W * Zs * Pm * Z₁ * Zs₁ = s • (W * Zs * Pm) := by
    rw [Matrix.mul_assoc (W * Zs * Pm), h2, Matrix.mul_smul, Matrix.mul_one]
  have e2 : W * Zs * Z * R₀ * Zs₁ = s • (W * R₀ * Zs₁) := by
    rw [Matrix.mul_assoc W Zs Z, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.smul_mul]
  have key : s • (W * Zs) * Pm - Pm * s • (W₁ * Zs₁) =
      W * Zs * (Pm * Z₁ - Z * R₀) * Zs₁ - s • ((Pm * W₁ - W * R₀) * Zs₁) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, smul_sub, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [e1, e2]
    abel
  rw [key, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_sub (hr _ _ (hl _ _ hA) i j) ((hr _ _ hB i j).mul_left s)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
