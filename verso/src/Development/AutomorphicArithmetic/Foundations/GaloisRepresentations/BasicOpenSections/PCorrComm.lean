import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `l _ p Y S S' B B' O g s bS β hS i bS' γ hcomm hl T w c c' hc hc' k j`. Take `⟨v, hv, hf, hb, hw⟩` from `hc`. Take `⟨v', hv', hf', hb', hw'⟩` from `hc'`. Establish `hsq : v' ≫ T.p = (c'.p ≫ i) ≫ s`. Rewrite using `[Category.assoc]`.

Conclude with `hv'.w`. Take `⟨u, huv, hup⟩ : ∃ u, u ≫ v = v' ∧ u ≫ c.p = c'.p ≫ i` from `⟨hv.lift v' (c'.p ≫ i) hsq, hv.lift_fst _ _ _, hv.lift_snd _ _ _⟩`. Substitute `huv` using the available equality. Establish `hpb : IsPullback u c'.p c.p i` using `IsPullback.of_right hv' hup hv`. Establish `hfu : c'.f ≫ i = u ≫ c.f`.

Apply `hS.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc]`. Rewrite using `[hf', hf, Category.assoc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hwu : c'.w = Wt.comap u c.w`.

Rewrite using `[hw', hw]`. Use function extensionality and compare the values at `Ω _ _ z`. Simplify using `only [Wt.comap, Category.assoc]`. Conclude with `TranscendenceTraces.corrBCQ_holds a8 l k j c' c i i u hpb hfu hwu hl`.
-/
theorem UpperTheory.Gal.Mod.corrComm :
    CorrComm := by
  intro l _ p Y S S' B B' O g s bS β hS i bS' γ hcomm hl T w c c' hc hc' k j
  obtain ⟨v, hv, hf, hb, hw⟩ := hc
  obtain ⟨v', hv', hf', hb', hw'⟩ := hc'
  have hsq : v' ≫ T.p = (c'.p ≫ i) ≫ s := by
    rw [Category.assoc]
    exact hv'.w
  obtain ⟨u, huv, hup⟩ : ∃ u, u ≫ v = v' ∧ u ≫ c.p = c'.p ≫ i :=
    ⟨hv.lift v' (c'.p ≫ i) hsq, hv.lift_fst _ _ _, hv.lift_snd _ _ _⟩
  subst huv
  have hpb : IsPullback u c'.p c.p i := IsPullback.of_right hv' hup hv
  have hfu : c'.f ≫ i = u ≫ c.f := by
    apply hS.hom_ext
    · simp only [Category.assoc]
      rw [hf', hf, Category.assoc]
    · calc (c'.f ≫ i) ≫ bS = (c'.f ≫ bS') ≫ γ := by rw [Category.assoc, hcomm, Category.assoc]
        _ = (c'.p ≫ bS') ≫ γ := by rw [hb']
        _ = c'.p ≫ i ≫ bS := by rw [Category.assoc, hcomm]
        _ = (u ≫ c.p) ≫ bS := by rw [hup, Category.assoc]
        _ = (u ≫ c.f) ≫ bS := by rw [Category.assoc, Category.assoc, hb]
  have hwu : c'.w = Wt.comap u c.w := by
    rw [hw', hw]
    funext Ω _ _ z
    simp only [Wt.comap, Category.assoc]
  exact TranscendenceTraces.corrBCQ_holds a8 l k j c' c i i u hpb hfu hwu hl
