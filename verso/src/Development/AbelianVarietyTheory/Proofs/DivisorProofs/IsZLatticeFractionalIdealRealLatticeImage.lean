import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify to obtain the desired conclusion from the available facts.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem span_range_remb (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli := (linearIndependent_monoidHom F ℝ).comp
    (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by
      ext a; exact congrArg (fun g : F →* ℝ => g a) h)
  have hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0 := by
    intro a
    have h1 : f (remb F a) = 0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    have h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ) := by
      ext σ
      simp [EuclideanSpace.single_apply, Pi.single_apply]
    rw [h2, map_sum] at h1
    simpa [mul_comm] using h1
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1))
    (by
      funext a
      simpa [Finset.sum_apply] using hsum a)
  apply hf0
  apply LinearMap.ext
  intro x
  have hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ) := by
    ext σ
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [hx, map_sum]
  simp [hcoef]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isZLattice_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)],
    IsZLattice ℝ (latOf N) := by
  intro F _ _ _ N hN _
  refine ⟨?_⟩
  rw [eq_top_iff, ← span_range_remb F, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hc : ∃ c ∈ N, c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hN
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h x, fun hx => hx ▸ (N : Submodule (𝓞 F) F).zero_mem⟩
  obtain ⟨c, hcN, hc0⟩ := hc
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ ℚ (L := F) {a / c}
  let α : 𝓞 F := ⟨y • (a / c), hint _ (Finset.mem_singleton_self _)⟩
  have hmem : (y : F) * a ∈ N := by
    have h := Submodule.smul_mem (N : Submodule (𝓞 F) F) α hcN
    have he : α • c = (y : F) * a := by
      rw [Algebra.smul_def]
      show (y • (a / c)) * c = (y : F) * a
      rw [zsmul_eq_mul]
      field_simp
    rw [he] at h
    exact h
  have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have heq : remb F a = (y : ℝ)⁻¹ • remb F ((y : F) * a) := by
    ext τ
    simp only [remb_apply, PiLp.smul_apply, smul_eq_mul, map_mul, map_intCast]
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latOf N _).2 ⟨_, hmem, rfl⟩))

end GlobalTheory.LipschitzTR
