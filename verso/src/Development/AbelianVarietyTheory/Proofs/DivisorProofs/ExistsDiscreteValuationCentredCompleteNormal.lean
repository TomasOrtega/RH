import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivVal

/- English proof (translation)
Use `haveI : IsNoetherianRing V := hV.1`. Distinguish the cases in `hm : maximalIdeal V = ⊥`. Use `⟨1, fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : algebraMap V (FractionRing V) v = 0`. Simplify using `[h]`.

Simplify using `[Valuation.one_apply_of_ne_zero h]`. Rewrite `hv` using `[hm, Ideal.mem_bot]`. Simplify using `[hv]`. Take `⟨T, hT, g, hg, hc⟩` from `GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V) (L := FractionRing V) (maximalIdeal V) hm`. Establish `hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v` using `fun v => by`.

Simplify using `using congrArg (fun f => f v) hg`. Establish `hne : maximalIdeal T ≠ ⊥` using `IsDiscreteValuationRing.not_a_field T`. Set `P : IsDedekindDomain.HeightOneSpectrum T` to `⟨maximalIdeal T, inferInstance, hne⟩`. Use `⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← hg']`.

Conclude with `P.valuation_le_one (g v)`. Rewrite using `[← hg']`. Use `(P.valuation_lt_one_iff_mem (g v)).2 ?_` and prove the remaining obligations. Use `show g v ∈ maximalIdeal T`. Rewrite using `[← Ideal.mem_comap, hc]`.

Conclude with `hv`.
-/
theorem exists_valuation_centre (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) :
    ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)),
      (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧
        ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  classical
  haveI : IsNoetherianRing V := hV.1
  by_cases hm : maximalIdeal V = ⊥
  · refine ⟨1, fun v => ?_, fun v hv => ?_⟩
    · by_cases h : algebraMap V (FractionRing V) v = 0
      · simp [h]
      · simp [Valuation.one_apply_of_ne_zero h]
    · rw [hm, Ideal.mem_bot] at hv
      simp [hv]
  · obtain ⟨T, hT, g, hg, hc⟩ := GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V)
      (L := FractionRing V) (maximalIdeal V) hm
    have hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v := fun v => by
      simpa using congrArg (fun f => f v) hg
    have hne : maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
    let P : IsDedekindDomain.HeightOneSpectrum T := ⟨maximalIdeal T, inferInstance, hne⟩
    refine ⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩
    · rw [← hg']
      exact P.valuation_le_one (g v)
    · rw [← hg']
      refine (P.valuation_lt_one_iff_mem (g v)).2 ?_
      show g v ∈ maximalIdeal T
      rw [← Ideal.mem_comap, hc]
      exact hv

end GlobalTheory.DivVal
