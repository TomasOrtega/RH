import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsHeckeLOfCompleted
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstOfGood
import Development.WeilBound.ThetaLifts.Reductions.WeightConstants.Bridge
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HeckeBridge GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
open GlobalTheory.CMVal (IsHeckeL IsCMType eulerFactor)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lInt2 : LInt2 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h χ hχ
  haveI := h.base.cm.2.1
  obtain ⟨H, hu, hloc, hinf⟩ := exists_hchar_unitary F E σ h.base.cm X.ν (isHecke_nu h)
  have hφ := isCMType_emb h.base.cm B.emb
  have hn := hinf _ _ (hasExp_nu h)
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have k0 := h.geo.kappa
  rcases hχ with rfl | rfl
  · obtain ⟨L, hL, hz⟩ := PositivityTheory.ThKRed.HK.heckeL_ne_zero hφ hu hn ⟨w₀, by have := k0 w₀; omega⟩
    exact ⟨L, hL.1, fun s hs => eq_charL hu hloc hL hs, fun z h1 => hz z fun w => by
      have := k0 w; have := le_abs_self (B.mα w - B.mβ w); omega⟩
  · have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
    obtain ⟨L, hL, hz⟩ := PositivityTheory.ThKRed.HK.heckeL_ne_zero hφ hu' (GlobalTheory.Published.HeckeFEModel.hasInf_inv hn) ⟨w₀, by have := k0 w₀; omega⟩
    refine ⟨L, hL.1, fun s hs => eq_charL hu' (fun W x => ?_) hL hs, fun z h1 => hz z fun w => by
      have := k0 w; have := le_abs_self (B.mα w - B.mβ w); rw [abs_neg]; omega⟩
    rw [Formalism.L2.Host.HChar.loc_inv, hloc]
    exact (map_inv Circle.toUnits _).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem constOfGood (hS : GlobalTheory.Published.StrongApproxSU) : ConstOfGood :=
  constOfGood_of hS GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds

end GlobalTheory.ThK.Dbl

end
