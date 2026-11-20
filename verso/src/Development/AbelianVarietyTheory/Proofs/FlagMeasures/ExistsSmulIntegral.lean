import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

open ValuativeRel

namespace GlobalTheory.SmulIntegralDenominator

/- English proof (translation)
Establish `h1 : IsAlgebraic K x` using `(Algebra.IsIntegral.isIntegral (R := K) x).isAlgebraic`. Establish `h2 : IsAlgebraic 𝒪[K] x` using `(IsFractionRing.isAlgebraic_iff 𝒪[K] K R).mpr h1`. Conclude with `h2.exists_integral_multiple`.
-/
theorem exists_smul_integral {K : Type} [Field K] [ValuativeRel K]
    {R : Type} [CommRing R] [Algebra K R] [Module.Finite K R] (x : R) :
    ∃ e : 𝒪[K], e ≠ 0 ∧ IsIntegral 𝒪[K] (e • x) := by
  have h1 : IsAlgebraic K x := (Algebra.IsIntegral.isIntegral (R := K) x).isAlgebraic
  have h2 : IsAlgebraic 𝒪[K] x := (IsFractionRing.isAlgebraic_iff 𝒪[K] K R).mpr h1
  exact h2.exists_integral_multiple

/- English proof (translation)
Use `haveI : Module.Finite K R := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Use `choose e he0 he using fun i => exists_smul_integral (K := K) (f i)`. Establish `hP : (∏ i, e i) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun i _ => he0 i`. Establish `hP' : ((∏ i, e i : 𝒪[K]) : K) ≠ 0` using `fun h => hP (Subtype.ext h)`. Use `⟨((∏ i, e i : 𝒪[K]) : K), (∏ i, e i).2, hP', fun i => ?_⟩` and prove the remaining obligations.

Use `⟨(∏ i, e i) • f i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[L.O_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]`. Conclude with `(he i).smul _`. Rewrite using `[Subring.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hP', map_one, one_mul]`.
-/
theorem common_denominator {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R)
    {ι : Type} [Fintype ι] (f : ι → R) :
    ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧
      ∀ i : ι, ∃ o ∈ L.O, f i = algebraMap K R e⁻¹ * o := by
  classical
  haveI : Module.Finite K R := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  choose e he0 he using fun i => exists_smul_integral (K := K) (f i)
  have hP : (∏ i, e i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => he0 i
  have hP' : ((∏ i, e i : 𝒪[K]) : K) ≠ 0 := fun h => hP (Subtype.ext h)
  refine ⟨((∏ i, e i : 𝒪[K]) : K), (∏ i, e i).2, hP', fun i => ?_⟩
  refine ⟨(∏ i, e i) • f i, ?_, ?_⟩
  · rw [L.O_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
    exact (he i).smul _
  · rw [Subring.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hP', map_one,
      one_mul]

/- English proof (translation)
Introduce `d1 K _ _ _ R _ _ _ L ι _ f`. Take `⟨e, he, he0, h⟩` from `common_denominator L f`. Conclude with `⟨e, he, he0, fun i => by obtain ⟨o, ho, hf⟩ := h i; exact ⟨o, ho, hf⟩⟩`.
-/
theorem main : (let d1 : {K : Type} → [inst : Field K] → [inst_1 : ValuativeRel K] → [inst_2 : TopologicalSpace K] → {R : Type} → [inst_3 : CommRing R] → [inst_4 : Algebra K R] → [inst_5 : TopologicalSpace R] → Formalism.MainNotions.S.Loc.LocE K R → K → R → Prop := @(fun {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) (γ : K) (x : R) ↦ ∃ o ∈ Formalism.MainNotions.S.Loc.LocE.O L, x = (Algebra.algebraMap K R : K → R) γ * o); ∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] {R : Type} [inst_3 : CommRing R] [inst_4 : Algebra K R] [inst_5 : TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R) {ι : Type} [Fintype ι] (f : ι → R), ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧ ∀ (i : ι), d1 L e⁻¹ (f i)) := by
  intro d1 K _ _ _ R _ _ _ L ι _ f
  obtain ⟨e, he, he0, h⟩ := common_denominator L f
  exact ⟨e, he, he0, fun i => by obtain ⟨o, ho, hf⟩ := h i; exact ⟨o, ho, hf⟩⟩

end GlobalTheory.SmulIntegralDenominator
