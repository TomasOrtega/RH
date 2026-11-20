import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PkPlaces

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W hW`. Establish `hl : (pk W).toLevCh.Is W.P.A3.A.μ0` using `hW.bot.hyp.2.2.2.1.lev`. Establish `hQQ : ∀ t, ∀ PP ∈ (pk W).Q t, ∀ PP' ∈ (pk W).Q t, ¬ Lev.IsConjPl PP PP'` using `fun t PP h PP' h' => ((hl.Q_pl t) PP h).2 PP' h'`. Establish `hnc : ∀ t, ∀ PP ∈ (pk W).Pg ∪ (pk W).Q t, ∀ PP' ∈ (pk W).Pg ∪ (pk W).Q t, ¬ Lev.IsConjPl PP PP'`. Introduce `t PP h PP' h' hc`.

Establish `ha` using `(GlobalTheory.StepLifts.places_apart _ hl t).1`. Break down `Finset.mem_union.1 h with h | h` into its components or cases. Conclude with `ha PP h PP' (Finset.mem_union.1 h') hc`. Break down `Finset.mem_union.1 h' with h' | h'` into its components or cases. Use `ha PP' h' PP (Or.inr h) ?_` and prove the remaining obligations.

Rewrite `hc`, the goal using `[GlobalTheory.GoodPrimes.isConjPl_iff]`. Rewrite using `[hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]`. Conclude with `hQQ t PP h PP' h' hc`. Use `⟨?_, fun t => ⟨(GlobalTheory.StepLifts.places_apart _ hl t).2, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Finset.union_empty]`.

Conclude with `GlobalTheory.CentralShift.exists_idemSum _ fun PP h PP' h' => (GlobalTheory.StepLifts.places_apart _ hl W.P.A3.A.μ0).1 PP h PP' (Or.inl h')`. Introduce `PP h PP' h' e`. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'` into its components or cases. Conclude with `Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart _ hl t).2 h (e' ▸ h')`. Conclude with `(GlobalTheory.StepLifts.places_apart _ hl t).1 PP h PP' (Or.inr h') (GlobalTheory.GoodPrimes.isConjPl_iff.2 e')`.

Conclude with `GlobalTheory.CentralShift.exists_idemSum _ (hnc t)`. Rewrite using `[Finset.empty_union]`. Conclude with `GlobalTheory.CentralShift.exists_idemSum _ (hQQ t)`.
-/
theorem pk_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → (∃ e : AE D, IsIdemSum e ((pk W).Pg ∪ ∅)) ∧ ∀ t, Disjoint (pk W).Pg ((pk W).Q t) ∧ (∀ PP ∈ (pk W).Pg, ∀ PP' ∈ (pk W).Q t, PP.under (𝓞 D.host.F) ≠ PP'.under (𝓞 D.host.F)) ∧ (∃ e : AE D, IsIdemSum e ((pk W).Pg ∪ (pk W).Q t)) ∧ ∃ e : AE D, IsIdemSum e (∅ ∪ (pk W).Q t) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have hl : (pk W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hQQ : ∀ t, ∀ PP ∈ (pk W).Q t, ∀ PP' ∈ (pk W).Q t, ¬ Lev.IsConjPl PP PP' :=
    fun t PP h PP' h' => ((hl.Q_pl t) PP h).2 PP' h'
  have hnc : ∀ t, ∀ PP ∈ (pk W).Pg ∪ (pk W).Q t, ∀ PP' ∈ (pk W).Pg ∪ (pk W).Q t, ¬ Lev.IsConjPl PP PP' := by
    intro t PP h PP' h' hc
    have ha := (GlobalTheory.StepLifts.places_apart _ hl t).1
    rcases Finset.mem_union.1 h with h | h
    · exact ha PP h PP' (Finset.mem_union.1 h') hc
    · rcases Finset.mem_union.1 h' with h' | h'
      · refine ha PP' h' PP (Or.inr h) ?_
        rw [GlobalTheory.GoodPrimes.isConjPl_iff] at hc ⊢
        rw [hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
      · exact hQQ t PP h PP' h' hc
  refine ⟨?_, fun t => ⟨(GlobalTheory.StepLifts.places_apart _ hl t).2, ?_, ?_, ?_⟩⟩
  · rw [Finset.union_empty]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun PP h PP' h' =>
      (GlobalTheory.StepLifts.places_apart _ hl W.P.A3.A.μ0).1 PP h PP' (Or.inl h')
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart _ hl t).2 h (e' ▸ h')
    · exact (GlobalTheory.StepLifts.places_apart _ hl t).1 PP h PP' (Or.inr h') (GlobalTheory.GoodPrimes.isConjPl_iff.2 e')
  · exact GlobalTheory.CentralShift.exists_idemSum _ (hnc t)
  · rw [Finset.empty_union]
    exact GlobalTheory.CentralShift.exists_idemSum _ (hQQ t)

end GlobalTheory.PkPlaces
