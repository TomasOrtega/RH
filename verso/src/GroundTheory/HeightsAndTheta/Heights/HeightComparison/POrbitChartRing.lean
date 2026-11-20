import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

/- English proof (translation)
Use `set T := Subfield.closure (Set.range (chartRatio x c))`. Set `T' : Subfield (AlgebraicClosure ℚ)` to `T.map (ratioField x).val.toRingHom`. Set `E : IntermediateField ℚ (AlgebraicClosure ℚ)` to `T'.toIntermediateField fun q ↦ by`. Rewrite using `[eq_ratCast]`. Conclude with `SubfieldClass.ratCast_mem T' q`.

Establish `hE : ratioField x ≤ E`. Use `IntermediateField.adjoin_le_iff.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i, j⟩, rfl⟩`. Use `⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩, div_mem (Subfield.subset_closure (Set.mem_range_self _)) (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩` and prove the remaining obligations. Simplify using `[chartRatio, div_div_div_cancel_right₀ (hc k)]`.

Take `⟨t, ht, hzt⟩` from `hE z.2`. Establish `: t = z` using `Subtype.ext hzt`. Conclude with `this ▸ ht`.
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
Introduce `ι _ _ n x c hc`. Use `⟨(Subalgebra.fg_iff_finiteType _).mp ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩` and prove the remaining obligations. Use `(isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩` and prove the remaining obligations. Use `isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_` and prove the remaining obligations. Conclude with `Subtype.ext h`.

Establish `hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring` using `Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp`. Take `⟨a, ha, b, hb, hab⟩` from `Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)`. Distinguish the cases in `hb0 : b = 0`. Use `⟨(0, 1), ?_⟩` and prove the remaining obligations. Rewrite `hab` using `[hb0, div_zero]`.

Simplify using `[← hab]`. Establish `hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0` using `fun h ↦ hb0 (congrArg Subtype.val h)`. Use `⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z * b = a`. Rewrite using `[← hab, div_mul_cancel₀ _ hb0]`.

Rewrite using `[Subtype.val_injective h]`.
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
The claim follows from `OrbitChartRing.proof Unit _ samplePoint _ fun _ ↦ by simp [samplePoint]`.
-/
example : Algebra.FiniteType ℤ (chartRing samplePoint (fun _ ↦ 0)) ∧
    IsFractionRing (chartRing samplePoint (fun _ ↦ 0)) (ratioField samplePoint) :=
  OrbitChartRing.proof Unit _ samplePoint _ fun _ ↦ by simp [samplePoint]

end

end GroundTheory.Heights₂.Heights
