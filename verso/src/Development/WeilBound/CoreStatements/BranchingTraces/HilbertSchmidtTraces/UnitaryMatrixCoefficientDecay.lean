import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

section

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {σ : Γ → (A →L[ℂ] A)}

/- English proof (translation)
Establish `hm : ∀ g k x, σ (g * k) x = σ g (σ k x)` using `fun g k x => by rw [h.mul]; rfl`. Use `⟨hm, fun g x y => ?_, h.norm, h.cont⟩` and prove the remaining obligations. Establish `hy : y = σ g (σ g⁻¹ y)` using `by rw [← hm, mul_inv_cancel, h.one]; rfl`. Use `conv_lhs => rw [hy]`. Conclude with `(LinearIsometry.mk (σ g : A →ₗ[ℂ] A) (h.norm g)).inner_map_map x _`.
-/
theorem uRep_of (h : IsU σ) : URep σ := by
  have hm : ∀ g k x, σ (g * k) x = σ g (σ k x) := fun g k x => by rw [h.mul]; rfl
  refine ⟨hm, fun g x y => ?_, h.norm, h.cont⟩
  have hy : y = σ g (σ g⁻¹ y) := by rw [← hm, mul_inv_cancel, h.one]; rfl
  conv_lhs => rw [hy]
  exact (LinearIsometry.mk (σ g : A →ₗ[ℂ] A) (h.norm g)).inner_map_map x _

variable [MeasurableSpace Γ] {ν : Measure Γ} {d : ℝ}

/- English proof (translation)
Establish `h` using `(hd.2 w u w u).2`. Simplify using `only [hu, zero_mul, integral_zero] at h`. Establish `hd0 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.1.ne'`. Break down `mul_eq_zero.1 ((div_eq_zero_iff.1 h.symm).resolve_right hd0) with h | h` into its components or cases. Conclude with `absurd (inner_self_eq_zero.1 h) hw`.

Conclude with `inner_self_eq_zero.1 h`.
-/
theorem eq_zero_of_orth (hd : IsFd ν σ d) {w u : A} (hw : w ≠ 0) (hu : ∀ g, ⟪u, σ g w⟫_ℂ = 0) : u = 0 := by
  have h := (hd.2 w u w u).2
  simp only [hu, zero_mul, integral_zero] at h
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  rcases mul_eq_zero.1 ((div_eq_zero_iff.1 h.symm).resolve_right hd0) with h | h
  · exact absurd (inner_self_eq_zero.1 h) hw
  · exact inner_self_eq_zero.1 h

end

end PositivityTheory.UnitaryDecomposition.X4
