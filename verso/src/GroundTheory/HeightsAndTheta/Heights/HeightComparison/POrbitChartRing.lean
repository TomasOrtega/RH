import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem mem_closure_chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (z : ratioField x) :
    z ∈ Subfield.closure (Set.range (chartRatio x c)) := by
  set T := Subfield.closure (Set.range (chartRatio x c))
  let T' : Subfield (AlgebraicClosure ℚ) := T.map (ratioField x).val.toRingHom
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    T'.toIntermediateField fun q ↦ by
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem T' q
  have hE : ratioField x ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    refine ⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩,
      div_mem (Subfield.subset_closure (Set.mem_range_self _))
        (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩
    simp [chartRatio, div_div_div_cancel_right₀ (hc k)]
  obtain ⟨t, ht, hzt⟩ := hE z.2
  have : t = z := Subtype.ext hzt
  exact this ▸ ht

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem OrbitChartRing.proof : OrbitChartRing.Statement := by
  intro ι _ _ n x c hc
  refine ⟨(Subalgebra.fg_iff_finiteType _).mp
    ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_
    exact Subtype.ext h
  · have hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring :=
      Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)
    by_cases hb0 : b = 0
    · refine ⟨(0, 1), ?_⟩
      rw [hb0, div_zero] at hab
      simp [← hab]
    · have hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      refine ⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      change z * b = a
      rw [← hab, div_mul_cancel₀ _ hb0]
  · rw [Subtype.val_injective h]

/- English proof (translation)
A detailed English derivation is pending.
-/
example : Algebra.FiniteType ℤ (chartRing samplePoint (fun _ ↦ 0)) ∧
    IsFractionRing (chartRing samplePoint (fun _ ↦ 0)) (ratioField samplePoint) :=
  OrbitChartRing.proof Unit _ samplePoint _ fun _ ↦ by simp [samplePoint]

end

end GroundTheory.Heights₂.Heights
