import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.KummerTwistLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D T L sc G μ₀ hL t q hq`. Take `⟨P, hP, rfl⟩` from `Finset.mem_image.1 hq`. Establish `hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0`. Simplify using `only [GlobalTheory.SqTop.twPl, Finset.mem_filter] at hP`. Break down `Finset.mem_union.1 hP.1 with h | h` into its components or cases.

Conclude with `absurd h hP.2`. Conclude with `⟨h, hP.2⟩`. Use `⟨⟨P, Formalism.DivisionValues.conjPl P, fun e => ?_, rfl, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `(hL.Q_pl t P hP'.1).2 P hP'.1` to reduce the goal to its premises. Introduce `c hc`.

Use `⟨Formalism.DivisionValues.cO _ c, ?_, rfl⟩` and prove the remaining obligations. Establish `h : Formalism.DivisionValues.cO _ c ∈ (Formalism.DivisionValues.conjPl P).asIdeal` using `Ideal.mem_map_of_mem _ hc`. Rewrite `h` using `[← e]`. Then use the resulting hypothesis. Conclude with `congrArg HeightOneSpectrum.asIdeal (GlobalTheory.TwistTypePlaces.under_conjPl P)`. Establish `hS : P.under (𝓞 D.host.F) ∉ G.pl.S0`.

Introduce `h`. Break down `G.pl.mem_S0_of_sum_eq.1 h with h0 | h1` into its components or cases. Conclude with `G.pl.levelPlace_ne_basePlace t P hP'.1 h0`. Apply `hP'.2` to reduce the goal to its premises. Rewrite using `[G.pl.w_Q t P hP'.1 h1]`.

Conclude with `Finset.mem_image_of_mem _ h`. Establish `h0` using `GlobalTheory.FunObj.SqNum.Model.expIn_condF G.pl (P.under (𝓞 D.host.F))`. Rewrite `h0` using `[if_neg hS]`. Conclude with `multiplicity_eq_zero.1 h0`.
-/
theorem twist_places_under_split_coprime_conductor : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL t q hq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter] at hP
    rcases Finset.mem_union.1 hP.1 with h | h
    · exact absurd h hP.2
    · exact ⟨h, hP.2⟩
  refine ⟨⟨P, Formalism.DivisionValues.conjPl P, fun e => ?_, rfl, ?_⟩, ?_⟩
  · apply (hL.Q_pl t P hP'.1).2 P hP'.1
    intro c hc
    refine ⟨Formalism.DivisionValues.cO _ c, ?_, rfl⟩
    have h : Formalism.DivisionValues.cO _ c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [← e] at h
  · exact congrArg HeightOneSpectrum.asIdeal (GlobalTheory.TwistTypePlaces.under_conjPl P)
  · have hS : P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
      intro h
      rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
      · exact G.pl.levelPlace_ne_basePlace t P hP'.1 h0
      · apply hP'.2
        rw [G.pl.w_Q t P hP'.1 h1]
        exact Finset.mem_image_of_mem _ h
    have h0 := GlobalTheory.FunObj.SqNum.Model.expIn_condF G.pl (P.under (𝓞 D.host.F))
    rw [if_neg hS] at h0
    exact multiplicity_eq_zero.1 h0

end GlobalTheory.KummerTwistLemmas
