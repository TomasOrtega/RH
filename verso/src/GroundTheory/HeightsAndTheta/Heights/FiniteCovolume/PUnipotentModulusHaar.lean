import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetSqEqOneOfPreservesBilin

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Module

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem det_sq_eq_one_of_preserves_bilin {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : LinearMap.det f ^ 2 = 1 :=
  _root_.UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin B hB f hf

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem measurePreserving_of_preserves_bilin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : MeasurePreserving f μ μ := by
  have h2 := det_sq_eq_one_of_preserves_bilin B hB f hf
  have hd : LinearMap.det f ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  have habs : |LinearMap.det f| = 1 := by
    have : |LinearMap.det f| ^ 2 = 1 := by rw [sq_abs]; exact h2
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 this
  refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, abs_inv, habs]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_eq_of_measurePreserving_coordinates {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (c : N → N) (hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map c = μ := by
  have hφ : Measurable φ := φ.continuous.measurable
  have key : ∀ T : V → V, MeasurePreserving T lam lam →
      (lam.map φ).map (φ ∘ T ∘ φ.symm) = lam.map φ := by
    intro T hT
    rw [Measure.map_map (hφ.comp (hT.measurable.comp φ.symm.continuous.measurable)) hφ]
    have : (φ ∘ T ∘ φ.symm) ∘ φ = φ ∘ T := by
      funext x
      simp
    rw [this, ← Measure.map_map hφ hT.measurable, hT.map_eq]
  have hinv : (lam.map φ).IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    have e : (fun x => n * x) = φ ∘ (fun x => φ.symm (n * φ x)) ∘ φ.symm := by
      funext x
      simp
    rw [e]
    exact key _ (hL n)
  have : IsFiniteMeasureOnCompacts (lam.map φ) := by
    refine ⟨fun K hK => ?_⟩
    have e := φ.toMeasurableEquiv.map_apply (μ := lam) K
    simp only [Homeomorph.toMeasurableEquiv_coe] at e
    rw [e]
    exact (φ.isCompact_preimage.2 hK).measure_lt_top
  have : (lam.map φ).IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
  have : (lam.map φ).IsHaarMeasure := {}
  rw [Measure.isMulLeftInvariant_eq_smul μ (lam.map φ), Measure.map_smul]
  congr 1
  have e : c = φ ∘ (fun x => φ.symm (c (φ x))) ∘ φ.symm := by
    funext x
    simp
  rw [e]
  exact key _ hC

end GroundTheory.Heights₂.Heights.FiniteCovolume
