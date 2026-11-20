import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Introduce `R _ φ lr π v w N d d' α β Q α₁ β₁ β₁' Q₁ R₁ R₀ h1 h2 h3 h4 h5`. Take `⟨u, hu_def⟩ : ∃ u : R, u = ((v ^ N * w ^ (2 * N))⁻¹ : Rˣ)` from `⟨_, rfl⟩`. Use `set s := (lr * (v : R)) ^ N with hs`. Use `set t := (lr * (w : R)) ^ N with ht`. Establish `hvw : u * ((v : R) ^ N * (w : R) ^ (2 * N)) = 1`.

Rewrite using `[hu_def, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, Units.inv_mul]`. Establish `hu : u * (s * (lr * (w : R)) ^ (2 * N)) = lr ^ (3 * N)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = lr ^ (3 * N) := by rw [hvw, one_mul]`. Use `⟨(u * t) • α, β₁', ?_⟩` and prove the remaining obligations. Use `set D4 := R₁ * α₁ - α * R₁.map φ with hD4def`. Use `set D5 := R₀ * β₁ - β * R₀.map φ with hD5def`. Establish `hD4 : α * R₁.map φ = R₁ * α₁ - D4` using `by rw [hD4def, sub_sub_cancel]`.

Establish `hD5 : β * R₀.map φ = R₀ * β₁ - D5` using `by rw [hD5def, sub_sub_cancel]`. Establish `e1 : t • (α * R₁.map φ * Q₁.map φ) = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.sub_mul, smul_sub, Matrix.mul_smul, Matrix.mul_assoc]`. Use `_ = R₁ * (s • (Q₁ * β₁)) - t • (D4 * Q₁.map φ) := by rw [h3]`.

Use `_ = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by`. Simplify using `only [Matrix.mul_smul, Matrix.mul_assoc]`. Establish `e2 : t • (α * Q.map φ * R₀.map φ) = s • (Q * R₀ * β₁) - s • (Q * D5)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_sub, smul_sub, Matrix.mul_assoc]`.

Establish `hmap : (R₁ * Q₁ - Q * R₀).map φ = R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ`. Rewrite using `[Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul]`. Establish `e3 : (u * t) • α * (R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ) = u • (t • (α * R₁.map φ * Q₁.map φ) - t • (α * Q.map φ * R₀.map φ))`. Simplify using `only [Matrix.smul_mul, Matrix.mul_sub, smul_sub, smul_smul, Matrix.mul_assoc]`. Establish `key : lr ^ (3 * N) • (R₁ * Q₁ - Q * R₀) - (u * t) • α * (R₁ * Q₁ - Q * R₀).map φ * β₁' = (u * t) • (D4 * (Q₁.map φ * β₁')) - (u * s) • (Q * (D5 * β₁'))`.

Rewrite using `[hmap, e3, e1, e2, ← hu]`. Simplify using `only [Matrix.sub_mul, Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_sub]`. Use `module`. Introduce `i j`. Rewrite using `[key, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply]`.

Use `dvd_sub (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h4 i k) _) _) (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right ?_ _) _)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.dvd_sum fun k' _ => dvd_mul_of_dvd_left (h5 k k') _`.
-/
theorem linkRec_holds : LinkRec := by
  intro R _ φ lr π v w N d d' α β Q α₁ β₁ β₁' Q₁ R₁ R₀ h1 h2 h3 h4 h5
  obtain ⟨u, hu_def⟩ : ∃ u : R, u = ((v ^ N * w ^ (2 * N))⁻¹ : Rˣ) := ⟨_, rfl⟩
  set s := (lr * (v : R)) ^ N with hs
  set t := (lr * (w : R)) ^ N with ht
  have hvw : u * ((v : R) ^ N * (w : R) ^ (2 * N)) = 1 := by
    rw [hu_def, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, Units.inv_mul]
  have hu : u * (s * (lr * (w : R)) ^ (2 * N)) = lr ^ (3 * N) := by
    calc u * (s * (lr * (w : R)) ^ (2 * N))
        = (u * ((v : R) ^ N * (w : R) ^ (2 * N))) * lr ^ (3 * N) := by
          rw [hs]
          ring
      _ = lr ^ (3 * N) := by rw [hvw, one_mul]
  refine ⟨(u * t) • α, β₁', ?_⟩
  set D4 := R₁ * α₁ - α * R₁.map φ with hD4def
  set D5 := R₀ * β₁ - β * R₀.map φ with hD5def
  have hD4 : α * R₁.map φ = R₁ * α₁ - D4 := by rw [hD4def, sub_sub_cancel]
  have hD5 : β * R₀.map φ = R₀ * β₁ - D5 := by rw [hD5def, sub_sub_cancel]
  have e1 : t • (α * R₁.map φ * Q₁.map φ) = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
    calc t • (α * R₁.map φ * Q₁.map φ) = t • ((R₁ * α₁ - D4) * Q₁.map φ) := by rw [hD4]
      _ = R₁ * (t • (α₁ * Q₁.map φ)) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.sub_mul, smul_sub, Matrix.mul_smul, Matrix.mul_assoc]
      _ = R₁ * (s • (Q₁ * β₁)) - t • (D4 * Q₁.map φ) := by rw [h3]
      _ = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have e2 : t • (α * Q.map φ * R₀.map φ) = s • (Q * R₀ * β₁) - s • (Q * D5) := by
    calc t • (α * Q.map φ * R₀.map φ) = (t • (α * Q.map φ)) * R₀.map φ := by rw [Matrix.smul_mul]
      _ = (s • (Q * β)) * R₀.map φ := by rw [h2]
      _ = s • (Q * (β * R₀.map φ)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = s • (Q * (R₀ * β₁ - D5)) := by rw [hD5]
      _ = s • (Q * R₀ * β₁) - s • (Q * D5) := by
        simp only [Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
  have hmap : (R₁ * Q₁ - Q * R₀).map φ = R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul]
  have e3 : (u * t) • α * (R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ)
      = u • (t • (α * R₁.map φ * Q₁.map φ) - t • (α * Q.map φ * R₀.map φ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_sub, smul_sub, smul_smul, Matrix.mul_assoc]
  have key : lr ^ (3 * N) • (R₁ * Q₁ - Q * R₀) - (u * t) • α * (R₁ * Q₁ - Q * R₀).map φ * β₁'
      = (u * t) • (D4 * (Q₁.map φ * β₁')) - (u * s) • (Q * (D5 * β₁')) := by
    rw [hmap, e3, e1, e2, ← hu]
    simp only [Matrix.sub_mul, Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_sub]
    module
  intro i j
  rw [key, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    Matrix.mul_apply, Matrix.mul_apply]
  refine dvd_sub (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h4 i k) _) _)
    (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right ?_ _) _)
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k' _ => dvd_mul_of_dvd_left (h5 k k') _

end UpperTheory.Gal.ClosedPhiFromClosedTrace
