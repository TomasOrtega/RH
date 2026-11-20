import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AdeleApprox

/- English proof (translation)
Take `⟨C, hC, hCy⟩` from `Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)`. Use `⟨C, hC, fun x => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2`. Take `⟨r, hr⟩` from `hCy (x.1 - algebraMap E _ u)`. Use `⟨u + r, ?_, ?_⟩` and prove the remaining obligations.

Use `show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C`. Rewrite using `[map_add, ← sub_sub]`. Conclude with `hr`. Establish `: x.2 - algebraMap E (Af E) (u + r) = (x.2 - algebraMap E _ u) - algebraMap E _ (r : E)` using `by rw [map_add, sub_sub] show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _`. Rewrite using `[this]`.

Conclude with `sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)`.
-/
theorem exists_compact_integral (E : Type) [Field E] [NumberField E] :
    ∃ C : Set (InfiniteAdeleRing E), IsCompact C ∧
      ∀ x : Ad E, ∃ a : E, (x - algebraMap E (Ad E) a).1 ∈ C ∧
        ∀ v, (x - algebraMap E (Ad E) a).2 v ∈ v.adicCompletionIntegers E := by
  obtain ⟨C, hC, hCy⟩ := Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap E _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C
    rw [map_add, ← sub_sub]
    exact hr
  · have : x.2 - algebraMap E (Af E) (u + r) =
        (x.2 - algebraMap E _ u) - algebraMap E _ (r : E) := by rw [map_add, sub_sub]
    show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

/- English proof (translation)
Introduce `E _ _ _ U hU`. Take `⟨C, hC, hcov⟩` from `exists_compact_integral E`. Take `⟨N, hN, hNU⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU`. Establish `hc : Continuous (infEq E).symm`. Use `continuous_pi fun w => ?_` and prove the remaining obligations.

Conclude with `(InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)`. Take `⟨B, hB⟩` from `isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded`. Use `⟨N * max B 0, by positivity, fun x => ?_⟩` and prove the remaining obligations. Establish `hN' : (N : E) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Take `⟨a, h1, h2⟩` from `hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)`.

Use `set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk`. Establish `e : x - algebraMap E (Ad E) ((N : E) * a) = N • k`. Rewrite using `[hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hN', map_one, one_mul, map_mul]`. Use `⟨(N : E) * a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_nsmul]`.

Establish `hb : ‖pInf E k‖ ≤ max B 0` using `(hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)`. Conclude with `(norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))`. Rewrite using `[e, map_nsmul]`. Conclude with `hNU _ h2`.
-/
theorem exists_rat_sub_bounded_small :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧
        pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  intro E _ _ _ U hU
  obtain ⟨C, hC, hcov⟩ := exists_compact_integral E
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU
  have hc : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded
  refine ⟨N * max B 0, by positivity, fun x => ?_⟩
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, h1, h2⟩ := hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)
  set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk
  have e : x - algebraMap E (Ad E) ((N : E) * a) = N • k := by
    rw [hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hN', map_one, one_mul, map_mul]
  refine ⟨(N : E) * a, ?_, ?_⟩
  · rw [e, map_nsmul]
    have hb : ‖pInf E k‖ ≤ max B 0 := (hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · rw [e, map_nsmul]
    exact hNU _ h2

end GlobalTheory.AdeleApprox
