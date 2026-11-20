import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherRest
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' J' n Ψ hv hP' hP hΨ hJ hJP`. Take `⟨h, a, hha, hhP, hvan⟩` from `hElim K ι K' ι' κ v P' J' n hv hP' hP hJ hJP`. Establish `hJh : IsMultiHomogIdeal (Ideal.span {h})` using `⟨{h}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hha⟩, rfl⟩`. Establish `hJhP : ¬ Ideal.span {h} ≤ imageZ v P'` using `fun hle => hhP (hle (Ideal.subset_span rfl))`. Use `measure_mono_null ?_ (projB_null Ψ hP hΨ hJh hJhP)` and prove the remaining obligations.

Introduce and unpack `y ⟨z', hz'P, hz'J, -, -, -, hΨy⟩`. Use `set w : (Σ k, ι k) → ℂ := fun p => z' (v p) with hw`. Establish `hw1 : (Ψ (segre w) 0)⁻¹ * Ψ (segre w) 0 = 1`. Use `congrFun hΨy 0` as an intermediate fact. Simplify `this` using `[map_smul]`.

Establish `h0 : Ψ (segre w) 0 ≠ 0` using `fun h0 => by simp [h0] at hw1`. Take `⟨k0⟩` from `hP.1`. Set `c : K → ℂ` to `Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre w) 0)⁻¹`. Establish `hc : ∀ k, c k ≠ 0`. Introduce `k`.

Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Simplify using `[c, h0]`. Simplify using `[c, Function.update_of_ne hk]`. Establish `hpc : ∏ k, c k = (Ψ (segre w) 0)⁻¹`.

Simplify using `[c, Finset.prod_update_of_mem (Finset.mem_univ k0)]`. Establish `hwP : w ∈ mcPts (imageZ v P')` using `IntersectionWithSection.comp_mem_mcPts hv hz'P`. Establish `hwh : w ∈ mcPts (Ideal.span {h})`. Use `⟨hwP.1, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton'.mp hf`.

Rewrite using `[map_mul, map_mul, hvan z' hz'P hz'J, mul_zero]`. Use `⟨fun p => c p.1 * w p, mcPts_smul hP.2.1.2.1 c hc hwP, mcPts_smul hJh c hc hwh, ?_⟩` and prove the remaining obligations. Rewrite using `[segre_smul, hpc]`. Conclude with `hΨy`.
-/
theorem PullbackVanishingOfNullCycle.proof (hElim : PullbackEliminationOfVariable.Statement) : PullbackVanishingOfNullCycle.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' J' n Ψ hv hP' hP hΨ hJ hJP
  obtain ⟨h, a, hha, hhP, hvan⟩ := hElim K ι K' ι' κ v P' J' n hv hP' hP hJ hJP
  have hJh : IsMultiHomogIdeal (Ideal.span {h}) :=
    ⟨{h}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hha⟩, rfl⟩
  have hJhP : ¬ Ideal.span {h} ≤ imageZ v P' := fun hle => hhP (hle (Ideal.subset_span rfl))
  refine measure_mono_null ?_ (projB_null Ψ hP hΨ hJh hJhP)
  rintro y ⟨z', hz'P, hz'J, -, -, -, hΨy⟩
  set w : (Σ k, ι k) → ℂ := fun p => z' (v p) with hw
  have hw1 : (Ψ (segre w) 0)⁻¹ * Ψ (segre w) 0 = 1 := by
    have := congrFun hΨy 0
    simpa [map_smul] using this
  have h0 : Ψ (segre w) 0 ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre w) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre w) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hwP : w ∈ mcPts (imageZ v P') := IntersectionWithSection.comp_mem_mcPts hv hz'P
  have hwh : w ∈ mcPts (Ideal.span {h}) := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hvan z' hz'P hz'J, mul_zero]
  refine ⟨fun p => c p.1 * w p, mcPts_smul hP.2.1.2.1 c hc hwP, mcPts_smul hJh c hc hwh, ?_⟩
  rw [segre_smul, hpc]
  exact hΨy

end GroundTheory.Heights₂.Heights.Inter
