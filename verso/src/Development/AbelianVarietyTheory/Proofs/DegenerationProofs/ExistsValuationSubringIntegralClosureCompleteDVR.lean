import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

namespace GlobalTheory.LN

open IsLocalRing

/- English proof (translation)
Set `K` to `FractionRing O`. Set `L : IntermediateField K F` to `IntermediateField.adjoin K {x}`. Use `haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Use `haveI : CharZero K := inferInstance`. Use `haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _`.

Use `haveI : IsDiscreteValuationRing (integralClosure O L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr O K L`. Use `haveI : IsFractionRing (integralClosure O L) L := integralClosure.isFractionRing_of_finite_extension K L`. Set `y : L` to `⟨x, IntermediateField.mem_adjoin_simple_self K x⟩`. Set `f : L →ₐ[O] F` to `(IntermediateField.val L).restrictScalars O`. Break down `ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩` into its components or cases.

Use `left`. Establish `h : IsIntegral O y` using `hz ▸ z.2`. Conclude with `h.map f`. Use `right`. Establish `h : IsIntegral O y⁻¹` using `hz ▸ z.2`.

Establish `h'` using `h.map f`. Rewrite `h'` using `[map_inv₀]`. Then use the resulting hypothesis.
-/
theorem isIntegral_or_isIntegral_inv (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F]
    [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (x : F) :
    IsIntegral O x ∨ IsIntegral O x⁻¹ := by
  let K := FractionRing O
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  haveI : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := inferInstance
  haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _
  haveI : IsDiscreteValuationRing (integralClosure O L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr O K L
  haveI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  let f : L →ₐ[O] F := (IntermediateField.val L).restrictScalars O
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    have h : IsIntegral O y := hz ▸ z.2
    exact h.map f
  · right
    have h : IsIntegral O y⁻¹ := hz ▸ z.2
    have h' := h.map f
    rwa [map_inv₀] at h'

/- English proof (translation)
Introduce `O _ _ _ ϖ h F _ _ _ _ _`. Break down `h with ⟨hF, -⟩ | ⟨hd, hirr, hc⟩` into its components or cases. Use `⟨⊤, fun x => ⟨fun _ => ?_, fun _ => trivial⟩⟩` and prove the remaining obligations. Establish `ha : IsAlgebraic O x` using `(IsFractionRing.isAlgebraic_iff O (FractionRing O) F).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Use `letI := hF.toField`.

Conclude with `ha.isIntegral`. Use `haveI : IsAdicComplete (maximalIdeal O) O := hirr.maximalIdeal_eq ▸ hc`. Conclude with `⟨⟨(integralClosure O F).toSubring, fun x => isIntegral_or_isIntegral_inv O F x⟩, fun x => Iff.rfl⟩`.
-/
theorem exists_valuationSubring_isIntegral : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  intro O _ _ _ ϖ h F _ _ _ _ _
  rcases h with ⟨hF, -⟩ | ⟨hd, hirr, hc⟩
  · refine ⟨⊤, fun x => ⟨fun _ => ?_, fun _ => trivial⟩⟩
    have ha : IsAlgebraic O x :=
      (IsFractionRing.isAlgebraic_iff O (FractionRing O) F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    letI := hF.toField
    exact ha.isIntegral
  · haveI : IsAdicComplete (maximalIdeal O) O := hirr.maximalIdeal_eq ▸ hc
    exact ⟨⟨(integralClosure O F).toSubring, fun x => isIntegral_or_isIntegral_inv O F x⟩,
      fun x => Iff.rfl⟩

end GlobalTheory.LN
