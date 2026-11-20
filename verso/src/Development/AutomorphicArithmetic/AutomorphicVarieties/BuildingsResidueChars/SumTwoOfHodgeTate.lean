import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `H hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'`. Take `⟨T⟩` from `Loc.tiedP l`. Establish `hv` using `GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)`. Establish `hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r')`. Use `Units.continuous_iff.2 ⟨hv, ?_⟩` and prove the remaining obligations.

Simplify using `only [← map_inv]`. Conclude with `hv.comp continuous_inv`. Establish `hht` using `hT E Ω l a b r r' C.cont C'.cont HT HT' C.ht C'.ht`. Use `⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, hht, fun w A h rc hrc => ?_⟩` and prove the remaining obligations. Take `⟨a1, b1⟩` from `C.par w A h rc hrc`.

Take `⟨a2, b2⟩` from `C'.par w A h rc hrc`. Use `⟨fun hw => hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ (a1 hw) (a2 hw), fun O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Take `⟨p1, e1⟩` from `b1 O Bw hj`. Take `⟨p2, e2⟩` from `b2 O Bw hj`. Establish `p3 : IsPstAt (Loc.PP l) Bw ((Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F` using `E) A).subtype) := by`.

Use `H.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val)) ?_` and prove the remaining obligations. Conclude with `(hht w A h O Bw hj).1`. Use `⟨p3, ?_⟩` and prove the remaining obligations. Establish `e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F` using `E) A).subtype = Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by`. Use extensionality with `g i j`.

Both sides reduce to the same expression. Rewrite `p3`, the goal using `[e]`. Rewrite using `[GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3]`. Conclude with `(Lev.ssCalc E Ω A w h).2.1 _ _ _ _ e1 e2`.
-/
theorem UpperTheory.sum_two_of_hodge_tate :
    HypothesesH → SumAway → SumHT → SumTwo := by
  intro H hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  have hht := hT E Ω l a b r r' C.cont C'.cont HT HT' C.ht C'.ht
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, hht, fun w A h rc hrc => ?_⟩
  obtain ⟨a1, b1⟩ := C.par w A h rc hrc
  obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
  refine ⟨fun hw => hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ (a1 hw) (a2 hw), fun O _ _ _ Bw hj => ?_⟩
  obtain ⟨p1, e1⟩ := b1 O Bw hj
  obtain ⟨p2, e2⟩ := b2 O Bw hj
  have p3 : IsPstAt (Loc.PP l) Bw ((Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype) := by
    refine H.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val)) ?_
    exact (hht w A h O Bw hj).1
  refine ⟨p3, ?_⟩
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e] at p3 ⊢
  rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3]
  exact (Lev.ssCalc E Ω A w h).2.1 _ _ _ _ e1 e2
