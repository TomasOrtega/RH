import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

/- English proof (translation)
Introduce `D`. Rewrite using `[Filter.eventually_cofinite]`. Establish `h2 : (2 : 𝓞 D.host.F) ≠ 0` using `two_ne_zero`. Establish `hB : (Ideal.span {(2 : 𝓞 D.host.F)}) ≠ 0`. Simplify `h2` using `[Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Establish `hfin2` using `Ideal.finite_factors hB`. Establish `hfinD` using `Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 D.host.F) (B := 𝓞 D.host.E))`. Establish `hfinU : ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) '' {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}).Finite` using `hfinD.image _`. Establish `hfinA : {v : Pl D | v.asIdeal ∈ (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) '' {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}}.Finite` using `hfinU.preimage (f := fun v : Pl D => v.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)`. Use `(hfinA.union hfin2).subset fun v hv => ?_` and prove the remaining obligations.

Distinguish the cases in `h : (2 : 𝓞 D.host.F) ∈ v.asIdeal`. Use `right`. Conclude with `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)`. Use `left`. Establish `hE : ¬ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v` using `fun hu => hv ⟨hu, h⟩`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt at hE`. Use `push_neg at hE`. Take `⟨P, hP, hL, hU⟩` from `hE`. Establish `hover : v.asIdeal = P.under (𝓞 D.host.F)` using `hL.over`. Establish `hPb : P ≠ ⊥`.

Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[hover, Ideal.under_bot]`. Use `⟨⟨P, hP, hPb⟩, ?_, hover.symm⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hd`.

Conclude with `hU (not_dvd_differentIdeal_iff.1 hd)`.
-/
theorem eventually_extUnram_two_notMem : ∀ D : D7, ∀ᶠ v : Pl D in cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D
  rw [Filter.eventually_cofinite]
  have h2 : (2 : 𝓞 D.host.F) ≠ 0 := two_ne_zero
  have hB : (Ideal.span {(2 : 𝓞 D.host.F)}) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using h2
  have hfin2 := Ideal.finite_factors hB
  have hfinD := Ideal.finite_factors
    (differentIdeal_ne_bot (A := 𝓞 D.host.F) (B := 𝓞 D.host.E))
  have hfinU : ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}).Finite := hfinD.image _
  have hfinA : {v : Pl D | v.asIdeal ∈ (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}}.Finite :=
    hfinU.preimage (f := fun v : Pl D => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (hfinA.union hfin2).subset fun v hv => ?_
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · right
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)
  · left
    have hE : ¬ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := fun hu => hv ⟨hu, h⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt at hE
    push_neg at hE
    obtain ⟨P, hP, hL, hU⟩ := hE
    have hover : v.asIdeal = P.under (𝓞 D.host.F) := hL.over
    have hPb : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover, Ideal.under_bot]
    refine ⟨⟨P, hP, hPb⟩, ?_, hover.symm⟩
    by_contra hd
    exact hU (not_dvd_differentIdeal_iff.1 hd)

end GlobalTheory.FinPl
