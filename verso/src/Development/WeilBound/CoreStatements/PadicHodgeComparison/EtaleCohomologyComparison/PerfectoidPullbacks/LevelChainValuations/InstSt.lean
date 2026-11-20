import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.unitB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.OkDvr
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CgLift
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.QbLePf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CgBasis
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.LevelSystemGood

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

/- English proof (translation)
The claim follows from `qb_le_pf hL M s`.
-/
theorem qb_le {L : Lev R m} (hL : L.Good) (M : Model l K) (s : ℕ) :
    ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T) := qb_le_pf hL M s

/- English proof (translation)
The claim follows from `unit_B_pf hL`.
-/
theorem unit_B {L : Lev R m} (hL : L.Good) : IsUnit ((l : L.B)) := unit_B_pf hL

/- English proof (translation)
The claim follows from `ok_dvr_pf`.
-/
theorem ok_dvr [FiniteDimensional ℚ_[l] K] : IsDomain (OK l K) ∧ IsDiscreteValuationRing (OK l K) ∧
    ∀ a : OK l K, a ≠ 0 → ∃ k : ℕ, a ∣ (l : OK l K) ^ k := ok_dvr_pf

/- English proof (translation)
The claim follows from `cg_basis_pf hL M hM s U hU j bs w`.
-/
theorem cg_basis {L : Lev R m} (hL : L.Good) (M : Model l K) (hM : M.Sm) (s : ℕ) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s)
    (j : ℕ) {a : ℕ} (bs : Module.Basis (Fin a) K (HdR M.q j)) (w : HO (QB L M s) j) :
    ∃! g : Fin a → L.B, w = ∑ t, g t • muB L.γB M.q 1 s {⊤} j (bs t) := cg_basis_pf hL M hM s U hU j bs w

/- English proof (translation)
The claim follows from `cg_lift_pf hL M hM s hs j`.
-/
theorem cg_lift [FiniteDimensional ℚ_[l] K] {L : Lev R m} (hL : L.Good) (M : Model l K) (hM : M.Sm) (s : ℕ) (hs : m ≤ s)
    (j : ℕ) : ∃ e : ℕ, LiftP (QA L M s) (l : L.A) s j e := cg_lift_pf hL M hM s hs j

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)

/- English proof (translation)
The claim follows from `level_system_good hL M s hM U hU hs rH hr`.
-/
theorem chain_good [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s) (hs : m ≤ s)
    (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
    (hr : ∀ n j x, trM (QA L M s) none (l : L.A) n j (rH (n + 1) j x) = rH n j ((M.HS false j).r n x)) :
    (chainOf hL M s (qb_le hL M s) rH).Good := level_system_good hL M s hM U hU hs rH hr

end

end CrystallineSemistableComparison.Pb.Kap
