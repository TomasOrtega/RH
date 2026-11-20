import Formalism.PeriodIntegrals.EfRankSum

namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps

/- English proof (translation)
Use `⟨fun r hr a b hab => ?_⟩` and prove the remaining obligations. Establish `hab' : r • a = r • b` using `hab`. Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Establish `hK : algebraMap O K r ≠ 0`. Simplify using `using (IsFractionRing.injective O K).ne hr0`.

Establish `h1 : (algebraMap O K r) • a = (algebraMap O K r) • b`. Rewrite using `[algebraMap_smul, algebraMap_smul]`. Conclude with `hab'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isTorsionFree_alg (O : Type) [CommRing O] [IsDomain O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O A := by
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • a = r • b := hab
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap O K r ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hr0
  have h1 : (algebraMap O K r) • a = (algebraMap O K r) • b := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hab'
  calc a = ((algebraMap O K r)⁻¹ * algebraMap O K r) • a := by rw [inv_mul_cancel₀ hK, one_smul]
    _ = ((algebraMap O K r)⁻¹ * algebraMap O K r) • b := by rw [mul_smul, h1, ← mul_smul]
    _ = b := by rw [inv_mul_cancel₀ hK, one_smul]

/- English proof (translation)
Take `⟨h⟩` from `isTorsionFree_alg O K A`. Use `⟨fun r hr a b hab => ?_⟩` and prove the remaining obligations. Establish `hab' : r • (a : A) = r • (b : A)`. Establish `h2` using `congrArg (fun x : ↥(As O A) => (x : A)) hab`. Simplify using `using h2`.

Conclude with `Subtype.ext (h hr hab')`.
-/
theorem isTorsionFree_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O ↥(As O A) := by
  obtain ⟨h⟩ := isTorsionFree_alg O K A
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • (a : A) = r • (b : A) := by
    have h2 := congrArg (fun x : ↥(As O A) => (x : A)) hab
    simpa using h2
  exact Subtype.ext (h hr hab')

/- English proof (translation)
Use `haveI := isTorsionFree_as O K A`. Conclude with `Module.free_of_finite_type_torsion_free'`.
-/
theorem free_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A]
    [Module.Finite O ↥(As O A)] : Module.Free O ↥(As O A) := by
  haveI := isTorsionFree_as O K A
  exact Module.free_of_finite_type_torsion_free'

/- English proof (translation)
Take `⟨htf⟩` from `isTorsionFree_alg O K A`. Use `IsLocalizedModule.mk ?_ ?_ ?_` and prove the remaining obligations. Introduce `s`. Establish `hs : algebraMap O K s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`. Rewrite using `[Module.End.isUnit_iff]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Simplify using `only [Module.algebraMap_end_apply] at hxy`. Conclude with `htf (isRegular_of_ne_zero (nonZeroDivisors.ne_zero s.2)) hxy`. Introduce `y`.

Use `⟨(algebraMap O K s)⁻¹ • y, ?_⟩` and prove the remaining obligations. Simplify using `only [Module.algebraMap_end_apply]`. Rewrite using `[← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]`. Introduce `y`. Establish `hy : IsAlgebraic K y` using `Algebra.IsAlgebraic.isAlgebraic y`.

Establish `hyO : IsAlgebraic O y` using `(IsFractionRing.isAlgebraic_iff O K A).mpr hy`. Take `⟨c, hc0, hc⟩` from `hyO.exists_integral_multiple`. Use `⟨(⟨c • y, hc⟩, ⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩), ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Introduce `x₁ x₂ h`.

Conclude with `⟨1, by rw [Subtype.ext h]⟩`.
-/
theorem isLocalizedModule_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A] :
    IsLocalizedModule (nonZeroDivisors O) ((As O A).val.toLinearMap) := by
  obtain ⟨htf⟩ := isTorsionFree_alg O K A
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro s
    have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp only [Module.algebraMap_end_apply] at hxy
      exact htf (isRegular_of_ne_zero (nonZeroDivisors.ne_zero s.2)) hxy
    · intro y
      refine ⟨(algebraMap O K s)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    have hy : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
    have hyO : IsAlgebraic O y := (IsFractionRing.isAlgebraic_iff O K A).mpr hy
    obtain ⟨c, hc0, hc⟩ := hyO.exists_integral_multiple
    refine ⟨(⟨c • y, hc⟩, ⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩), ?_⟩
    rfl
  · intro x₁ x₂ h
    exact ⟨1, by rw [Subtype.ext h]⟩

/- English proof (translation)
Use `haveI : Module.Free O ↥(As O A) := free_as O K A`. Use `haveI := isLocalizedModule_as O K A`. Set `b` to `Module.Free.chooseBasis O ↥(As O A)`. Set `b'` to `b.ofIsLocalizedModule K (nonZeroDivisors O) ((As O A).val.toLinearMap)`. Rewrite using `[Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']`.
-/
theorem finrank_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    [Module.Finite O ↥(As O A)] : Module.finrank O ↥(As O A) = Module.finrank K A := by
  haveI : Module.Free O ↥(As O A) := free_as O K A
  haveI := isLocalizedModule_as O K A
  let b := Module.Free.chooseBasis O ↥(As O A)
  let b' := b.ofIsLocalizedModule K (nonZeroDivisors O) ((As O A).val.toLinearMap)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end PI.UnitaryGroupMassFormula.EfRankSum
