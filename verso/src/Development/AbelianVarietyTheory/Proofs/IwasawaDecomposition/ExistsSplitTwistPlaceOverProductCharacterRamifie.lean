import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSplitPlace

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isSplitPl_of_not_isConjPl (D : D7) (P : PlE D.host) (h : ¬ Formalism.IndefR.Lev.IsConjPl P P) : IsSplitPl D.host P := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun y hy hm => h y hm (hy.trans (GlobalTheory.DimPartsCompare.star_conj _).symm)⟩

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_splitPlace_of_mem_qPl : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
  rintro D T L μ0 hL i t v ⟨hg, w, hw, hn⟩
  have hu : (L.C.mu0 i).UnrAt w := (L.C.isMu0 i).unr w fun k hk => hg ⟨w, hw, k, hk⟩
  have hx : ¬ (L.xiH t).UnrAt w := fun h => hn fun x hx => by
    rw [Formalism.L2.Host.HChar.loc_mul, hu x hx, h x hx, one_mul]
  have key : ∀ P ∈ L.Q t, NG.OverPl P v → ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
    intro P hP hov
    obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D P
      (isSplitPl_of_not_isConjPl D P ((hL.Q_pl t P hP).2 P hP))
    refine ⟨s, HeightOneSpectrum.ext ?_, hs ▸ hP⟩
    rw [← s.w_under, hs]
    exact hov
  rcases (hL.Q_ram t w).1 hx with h | ⟨P, hP, hc⟩
  · exact key w h hw
  · refine key P hP ?_
    rw [GlobalTheory.DimPartsCompare.eq_cPl_of_isConjPl hc]
    exact (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.DimPartsCompare.under_cPl w)).trans hw

end GlobalTheory.TwistSplitPlace
