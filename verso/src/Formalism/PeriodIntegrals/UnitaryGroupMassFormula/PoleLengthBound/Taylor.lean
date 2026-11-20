import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AssembleAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

/- English proof (translation)
Introduce `k x hx`. Take `⟨cf, hcf⟩` from `PoleLengthBounds.pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF)) (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx`. Use `⟨fun α => cf α.1, 0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[add_zero, hcf]`. Conclude with `(Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) k) (fun α => (∏ i, sfr X la G.w i.succ ^ α i) • cf α)).symm`.
-/
theorem taylor_holds (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Taylor G la := by
  intro k x hx
  obtain ⟨cf, hcf⟩ := PoleLengthBounds.pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨fun α => cf α.1, 0, Submodule.zero_mem _, ?_⟩
  rw [add_zero, hcf]
  exact (Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) k)
    (fun α => (∏ i, sfr X la G.w i.succ ^ α i) • cf α)).symm

end PI.PoleLengthCount
