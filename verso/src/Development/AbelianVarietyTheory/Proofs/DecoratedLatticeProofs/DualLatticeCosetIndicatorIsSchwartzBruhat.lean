import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicator

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetSB

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ q L _ f`. Use `haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k`. Distinguish the cases in `hex : ∃ F : n → k, Lifts L F f`. Take `⟨F, hF⟩` from `hex`. Establish `e : cosetInd q L f = fun η => dualInd L (η - q.inv • F)`.

Use function extensionality and compare the values at `η`. Rewrite using `[← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]`. Rewrite using `[e]`. Conclude with `GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F) (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _`. Establish `e : cosetInd q L f = 0` using `by classical`.

Use function extensionality and compare the values at `η`. Unfold `cosetInd`. Rewrite using `[if_neg fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(SB (n → k)).zero_mem`.
-/
theorem cosetInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  intro k _ _ _ _ n _ _ q L _ f
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  by_cases hex : ∃ F : n → k, Lifts L F f
  · obtain ⟨F, hF⟩ := hex
    have e : cosetInd q L f = fun η => dualInd L (η - q.inv • F) := by
      funext η
      rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]
    rw [e]
    exact GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F)
      (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _
  · have e : cosetInd q L f = 0 := by
      classical
      funext η
      unfold cosetInd
      rw [if_neg fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]
      rfl
    rw [e]
    exact (SB (n → k)).zero_mem

end GlobalTheory.FinPl.CosetSB
