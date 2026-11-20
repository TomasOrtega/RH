import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestComplement

/- English proof (translation)
Introduce `F _ _ v κ _ φ hφ`. Take `⟨f, hf⟩` from `GlobalTheory.TensUniq.exists_sInf_ne_zero F κ`. Set `φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ` to `fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1`. Establish `hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `Filter.Eventually.of_forall fun _ => rfl`. Take `⟨r, hr, hrt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f φs hstd`.

Establish `hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r`. Use `⟨hr, ?_⟩` and prove the remaining obligations. Rewrite using `[hrt φ]`. Use `GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hφ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `GlobalTheory.StdVacuum.indicator_mem_SB w`.

Use `⟨r, hRest, 0, ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun (hrt (fun _ => 1)) 0`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e`. Rewrite using `[e]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure`.

Establish `hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0`. Use function extensionality and compare the values at `i`. Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0`. Conclude with `map_zero _`. Establish `hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1`.

Use `finprod_eq_one_of_forall_eq_one fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Rewrite using `[Function.update_of_ne hw]`.

Simplify using `only [φs, Pi.zero_apply, map_zero]`. Rewrite using `[Set.indicator_of_mem (by intro i; exact zero_mem _)]`. Both sides reduce to the same expression. Rewrite using `[hI, hP, mul_one]`. Conclude with `hf`.
-/
theorem exists_rest_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (f : (κ → Fv F v) → ℂ), f ∈ GlobalTheory.WeilM.SB (κ → Fv F v) →
    ∃ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r ∧ ∃ x₀, r x₀ ≠ 0 := by
  intro F _ _ v κ _ φ hφ
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r := by
    refine ⟨hr, ?_⟩
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  refine ⟨r, hRest, 0, ?_⟩
  have e := congrFun (hrt (fun _ => 1)) 0
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
  rw [e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
    exact map_zero _
  have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]
    · rw [Function.update_of_ne hw]
      simp only [φs, Pi.zero_apply, map_zero]
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  rw [hI, hP, mul_one]
  exact hf

end GlobalTheory.RestComplement
