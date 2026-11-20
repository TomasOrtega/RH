import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/- English proof (translation)
Establish `h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity`. Rewrite using `[Matrix.frobenius_norm_def]`. Simplify using `only [Real.rpow_two]`. Rewrite using `[← Real.sqrt_eq_rpow, Real.sq_sqrt h0]`. Both sides reduce to the same expression.
-/
theorem hs_eq_frobenius_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs A = ‖A‖ ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  rfl

/- English proof (translation)
Set `Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ)` to `{ toFun := fun A => (A * X - X * A, A *ᵥ v) map_add' := fun A B => by ext1`. Simplify using `only [Prod.fst_add, add_mul, mul_add]`. Normalize the expressions using the abelian group laws. Simplify using `only [Prod.snd_add, Matrix.add_mulVec]`. Use the proof step `map_smul' := fun a A => by ext1`.

Simplify using `[smul_sub]`. Simplify using `[Matrix.smul_mulVec] }`. Establish `hker : LinearMap.ker Φ = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `A hA`.

Establish `h1 : A * X - X * A = 0` using `congrArg Prod.fst hA`. Establish `h2 : A *ᵥ v = 0` using `congrArg Prod.snd hA`. Conclude with `h A (sub_eq_zero.mp h1) h2`. Take `⟨K, hK, hanti⟩` from `LinearMap.exists_antilipschitzWith Φ hker`. Use `⟨(K : ℝ) ^ 2, by positivity, fun A hA => ?_⟩` and prove the remaining obligations.

Establish `hle : ‖A‖ ≤ K * ‖A * X - X * A‖`. Establish `h3` using `hanti.le_mul_dist A 0`. Rewrite `h3` using `[map_zero, dist_zero_right, dist_zero_right]`. Establish `h4 : ‖Φ A‖ = ‖A * X - X * A‖`. Express the relevant statement in the definitionally equal form `‖((A * X - X * A, A *ᵥ v) : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ))‖ = _`.

Rewrite using `[hA, Prod.norm_def]`. Simplify using the standard rewrite rules. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis. Rewrite using `[hs_eq_frobenius_sq, hs_eq_frobenius_sq, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hle 2`.
-/
theorem hs_le_commutator {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (h : ∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 →
      Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  let Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) :=
    { toFun := fun A => (A * X - X * A, A *ᵥ v)
      map_add' := fun A B => by
        ext1
        · simp only [Prod.fst_add, add_mul, mul_add]; abel
        · simp only [Prod.snd_add, Matrix.add_mulVec]
      map_smul' := fun a A => by
        ext1
        · simp [smul_sub]
        · simp [Matrix.smul_mulVec] }
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have h1 : A * X - X * A = 0 := congrArg Prod.fst hA
    have h2 : A *ᵥ v = 0 := congrArg Prod.snd hA
    exact h A (sub_eq_zero.mp h1) h2
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith Φ hker
  refine ⟨(K : ℝ) ^ 2, by positivity, fun A hA => ?_⟩
  have hle : ‖A‖ ≤ K * ‖A * X - X * A‖ := by
    have h3 := hanti.le_mul_dist A 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h3
    have h4 : ‖Φ A‖ = ‖A * X - X * A‖ := by
      change ‖((A * X - X * A, A *ᵥ v) : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ))‖ = _
      rw [hA, Prod.norm_def]
      simp
    rwa [h4] at h3
  rw [hs_eq_frobenius_sq, hs_eq_frobenius_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

end GlobalTheory.CompanionTheory.RgHeFrame
