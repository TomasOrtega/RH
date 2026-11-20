import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfUnramifiedOverPlaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotDvdDifferentIdealOfStandardAddCharUnramifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TripleRam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `h`. Use `h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩` and prove the remaining obligations. Establish `he : ε = GlobalTheory.EmbChart.atPlace v 1`. Take `⟨α, rfl, h1, h0⟩` from `hε`. Rewrite using `[GlobalTheory.EmbChart.atPlace_apply]`.

Use `congr 1`. Use `FiniteAdeleRing.ext _ fun u => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)`. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality.

Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self, h1]`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]`. Rewrite using `[he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]`. Both sides reduce to the same expression.
-/
theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]; rfl

/- English proof (translation)
Introduce `hu`. Use `v.isPrime` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `(Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some`. Set `w : HeightOneSpectrum (𝓞 D.host.E)` to `⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩`. Establish `hw : w.under (𝓞 D.host.F) = v` using `HeightOneSpectrum.ext hl.over.symm`.

Conclude with `h w hw (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D χ v ε hε hu w hw)`.
-/
theorem not_unramAt_of_forall {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → ¬ GlobalTheory.LFun.UnrAt χ w) :
    ¬ GlobalTheory.WeilParts.UnramAt ε χ := by
  intro hu
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  exact h w hw (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D χ v ε hε hu w hw)

/- English proof (translation)
Introduce `D T L sc G μ₀ hL W t i j hS M hM en Bs Γ X om om' hX hT v ε hε`. Distinguish the cases in `hv : v ∈ X.T`. Use `right`. Establish `hP : v ∈ Bs.P` using `hT.chars.sub hv`. Use `⟨not_nonSplitAt_of_emb hε (Bs.τ ⟨v, hP⟩), ?_, GlobalTheory.T.not_dvd_differentIdeal_of_standardAddChar_unramified hT.base.std (hT.base.psiP v hP)⟩` and prove the remaining obligations.

Rewrite using `[← hX.α, ← hX.β]`. Conclude with `not_unramAt_of_forall hε fun w hw => hT.chars.ram w (hw ▸ hv)`. Use `left`. Rewrite using `[← hX.α, ← hX.β]`. Conclude with `⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place hε fun w hw => hT.chars.unrα w (fun h => hv (hw ▸ h)), GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place hε fun w hw => hT.chars.unrβ w (fun h => hv (hw ▸ h))⟩`.
-/
theorem ram_clause : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ (M : Vol G), M.Is t → ∀ (en : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G ↑i ↑j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G ↑i ↑j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) om om',
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t ↑i ↑j en Bs Γ X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j) ∧ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j)) ∨
      (¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL W t i j hS M hM en Bs Γ X om om' hX hT v ε hε
  by_cases hv : v ∈ X.T
  · right
    have hP : v ∈ Bs.P := hT.chars.sub hv
    refine ⟨not_nonSplitAt_of_emb hε (Bs.τ ⟨v, hP⟩), ?_, GlobalTheory.T.not_dvd_differentIdeal_of_standardAddChar_unramified hT.base.std (hT.base.psiP v hP)⟩
    rw [← hX.α, ← hX.β]
    exact not_unramAt_of_forall hε fun w hw => hT.chars.ram w (hw ▸ hv)
  · left
    rw [← hX.α, ← hX.β]
    exact ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place hε fun w hw => hT.chars.unrα w (fun h => hv (hw ▸ h)),
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place hε fun w hw => hT.chars.unrβ w (fun h => hv (hw ▸ h))⟩

end GlobalTheory.TripleRam

end
