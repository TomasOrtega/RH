import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

/- English proof (translation)
Introduce `m g d v hg hd hv A hc hAv`. Establish `h1 : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g hg`. Establish `h2 : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hg`. Take `⟨M, hM⟩ : ∃ M, M = g⁻¹ * A * g` from `⟨_, rfl⟩`. Establish `hcomm : M * diagonal d = diagonal d * M`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hM]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h1, Matrix.mul_one]`. Use `_ = g⁻¹ * ((g * diagonal d * g⁻¹) * A) * g := by rw [hc]`.

Use `_ = diagonal d * M := by`. Rewrite using `[hM]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc g⁻¹ g, h1, Matrix.one_mul]`. Establish `hdiag : ∀ i k, i ≠ k → M i k = 0`.

Introduce `i k hik`. Establish `h` using `congrFun (congrFun hcomm i) k`. Rewrite `h` using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Establish `h3 : M i k * (d k - d i) = 0` using `by rw [mul_sub, h]; ring`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases.

Conclude with `h4`. Conclude with `absurd (hd (sub_eq_zero.mp h4)).symm hik`. Establish `hMg : M * g⁻¹ = g⁻¹ * A`. Rewrite using `[hM, Matrix.mul_assoc, h2, Matrix.mul_one]`. Establish `hMv : M *ᵥ (g⁻¹ *ᵥ v) = 0`.

Rewrite using `[Matrix.mulVec_mulVec, hMg, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]`. Establish `hM0 : M = 0`. Use extensionality with `i k`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Establish `h` using `congrFun hMv i`. Establish `h5 : M i i * (g⁻¹ *ᵥ v) i = 0`. Establish `h6 : (M *ᵥ (g⁻¹ *ᵥ v)) i = M i i * (g⁻¹ *ᵥ v) i`. Rewrite using `[Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_eq_single i (fun j _ hj => by rw [hdiag i j (Ne.symm hj), zero_mul]) (fun h => absurd (Finset.mem_univ i) h)`.

Rewrite using `[← h6, h]`. Both sides reduce to the same expression. Simplify using `using (mul_eq_zero.mp h5).resolve_right (hv i)`. Simplify using `using hdiag i k hik`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]`. Use `_ = 0 := by rw [← hM, hM0, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem commutant_cyclic_eq_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ),
    IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) →
    ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A →
      A *ᵥ v = 0 → A = 0 := by
  intro m g d v hg hd hv A hc hAv
  have h1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have h2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  obtain ⟨M, hM⟩ : ∃ M, M = g⁻¹ * A * g := ⟨_, rfl⟩
  have hcomm : M * diagonal d = diagonal d * M := by
    calc M * diagonal d = g⁻¹ * (A * (g * diagonal d * g⁻¹)) * g := by
          rw [hM]
          simp only [Matrix.mul_assoc]
          rw [h1, Matrix.mul_one]
      _ = g⁻¹ * ((g * diagonal d * g⁻¹) * A) * g := by rw [hc]
      _ = diagonal d * M := by
          rw [hM]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc g⁻¹ g, h1, Matrix.one_mul]
  have hdiag : ∀ i k, i ≠ k → M i k = 0 := by
    intro i k hik
    have h := congrFun (congrFun hcomm i) k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h3 : M i k * (d k - d i) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd (hd (sub_eq_zero.mp h4)).symm hik
  have hMg : M * g⁻¹ = g⁻¹ * A := by
    rw [hM, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hMv : M *ᵥ (g⁻¹ *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hMg, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]
  have hM0 : M = 0 := by
    ext i k
    by_cases hik : i = k
    · subst hik
      have h := congrFun hMv i
      have h5 : M i i * (g⁻¹ *ᵥ v) i = 0 := by
        have h6 : (M *ᵥ (g⁻¹ *ᵥ v)) i = M i i * (g⁻¹ *ᵥ v) i := by
          rw [Matrix.mulVec, dotProduct]
          exact Finset.sum_eq_single i (fun j _ hj => by rw [hdiag i j (Ne.symm hj), zero_mul])
            (fun h => absurd (Finset.mem_univ i) h)
        rw [← h6, h]; rfl
      simpa using (mul_eq_zero.mp h5).resolve_right (hv i)
    · simpa using hdiag i k hik
  calc A = g * (g⁻¹ * A * g) * g⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = 0 := by rw [← hM, hM0, Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.CompanionTheory.RgHeFrame
