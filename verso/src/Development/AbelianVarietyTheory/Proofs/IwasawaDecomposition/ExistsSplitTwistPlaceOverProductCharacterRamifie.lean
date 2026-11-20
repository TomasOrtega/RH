import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSplitPlace

/- English proof (translation)
Unfold `Formalism.IndefR.Lev.IsConjPl at h`. Use `push Not at h`. Take `⟨c, hc, h⟩` from `h`. Conclude with `⟨c, hc, fun y hy hm => h y hm (hy.trans (GlobalTheory.DimPartsCompare.star_conj _).symm)⟩`.
-/
theorem isSplitPl_of_not_isConjPl (D : D7) (P : PlE D.host) (h : ¬ Formalism.IndefR.Lev.IsConjPl P P) : IsSplitPl D.host P := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun y hy hm => h y hm (hy.trans (GlobalTheory.DimPartsCompare.star_conj _).symm)⟩

/- English proof (translation)
Introduce and unpack `D T L μ0 hL i t v ⟨hg, w, hw, hn⟩`. Establish `hu : (L.C.mu0 i).UnrAt w` using `(L.C.isMu0 i).unr w fun k hk => hg ⟨w, hw, k, hk⟩`. Establish `hx : ¬ (L.xiH t).UnrAt w` using `fun h => hn fun x hx => by`. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, hu x hx, h x hx, one_mul]`. Establish `key : ∀ P ∈ L.Q t, NG.OverPl P v → ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t`.

Introduce `P hP hov`. Take `⟨s, hs⟩` from `GlobalTheory.OffBad.splitPlace_of_isSplitPl D P (isSplitPl_of_not_isConjPl D P ((hL.Q_pl t P hP).2 P hP))`. Use `⟨s, HeightOneSpectrum.ext ?_, hs ▸ hP⟩` and prove the remaining obligations. Rewrite using `[← s.w_under, hs]`. Conclude with `hov`.

Break down `(hL.Q_ram t w).1 hx with h | ⟨P, hP, hc⟩` into its components or cases. Conclude with `key w h hw`. Use `key P hP ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.DimPartsCompare.eq_cPl_of_isConjPl hc]`. Conclude with `(congrArg HeightOneSpectrum.asIdeal (GlobalTheory.DimPartsCompare.under_cPl w)).trans hw`.
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
