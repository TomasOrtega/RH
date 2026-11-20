import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocalFieldPow

open ValuativeRel in

/- English proof (translation)
Introduce `k _ _ _ _`. Take `⟨r, hr0, hr1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`. Establish `hr : r ≠ 0` using `by simpa using hr0`. Establish `: MulArchimedean (ValueGroupWithZero k)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Use `⟨Units.mk0 r hr, ?_⟩` and prove the remaining obligations.

Rewrite using `[(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]`. Introduce `γ hγ`. Take `⟨m, hm⟩` from `exists_pow_lt₀ hr1 (Units.mk0 γ hγ)`. Rewrite `hm` using `[Units.val_mk0]`. Use `filter_upwards [eventually_ge_atTop m] with n hn`.

Establish `h : valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ valuation k r ^ m`. Simplify using `using pow_le_pow_of_le_one zero_le' hr1.le hn`. Simplify using `using lt_of_le_of_lt h hm`.
-/
theorem exists_unit_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  intro k _ _ _ _
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr : r ≠ 0 := by simpa using hr0
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨Units.mk0 r hr, ?_⟩
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  rw [Units.val_mk0] at hm
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ valuation k r ^ m := by
    simpa using pow_le_pow_of_le_one zero_le' hr1.le hn
  simpa using lt_of_le_of_lt h hm

end GlobalTheory.CompanionTheory.LocalFieldPow
