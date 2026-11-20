import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.PolChar

open Formalism.L2.Host

section Comp

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ideleInf : (AdeleRing (𝓞 E) E)ˣ →* InfiniteAdeleRing E :=
  (MonoidHom.fst _ _).comp (Units.coeHom (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

def ideleAt (u : HeightOneSpectrum (𝓞 E)) : (AdeleRing (𝓞 E) E)ˣ →* u.adicCompletion E :=
  (RestrictedProduct.evalMonoidHom _ u).comp
    ((MonoidHom.snd _ _).comp (Units.coeHom (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)))

/- English proof (translation)
Use `Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))` and prove the remaining obligations. Use `Eq.trans ?_ (map_prod (ideleInf E) _ _).symm` and prove the remaining obligations. Use `Eq.trans ?_ (Finset.prod_eq_one fun w _ => rfl).symm` and prove the remaining obligations. Conclude with `map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E)`. Use `Eq.trans ?_ (map_prod (ideleAt E u) _ _).symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E u (Neutral.B1.finiteSingle F v (algebraMap F _ (a : F)) (u.under (𝓞 F))) = ∏ w ∈ aboveF (L := E) F v, Neutral.B1.finiteSingle E w (algebraMap E _ (algebraMap F E a)) u`. Distinguish the cases in `h : u.under (𝓞 F) = v`. Establish `hu : u ∈ aboveF (L` using `E) F v := by simp [aboveF, h]`. Rewrite using `[Finset.prod_eq_single_of_mem u hu fun w _ hw => GlobalTheory.LFun.finSingle_ne (Ne.symm hw) _, GlobalTheory.LFun.finSingle_self]`. Substitute `h` using the available equality.

Rewrite using `[GlobalTheory.LFun.finSingle_self, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]`. Rewrite using `[GlobalTheory.LFun.finSingle_ne h, map_one]`. Use `(Finset.prod_eq_one fun w hw => GlobalTheory.LFun.finSingle_ne ?_ _).symm` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `h (by simpa [aboveF] using hw)`.
-/
theorem ideleMap_localIdele_atFin (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (Neutral.B1.localIdele F v (atFin v a)) =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.localIdele E w (atFin w (upF F a)) := by
  classical
  refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
  · refine Eq.trans ?_ (map_prod (ideleInf E) _ _).symm
    refine Eq.trans ?_ (Finset.prod_eq_one fun w _ => rfl).symm
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E)
  · refine Eq.trans ?_ (map_prod (ideleAt E u) _ _).symm
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E u
        (Neutral.B1.finiteSingle F v (algebraMap F _ (a : F)) (u.under (𝓞 F))) =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.finiteSingle E w (algebraMap E _ (algebraMap F E a)) u
    by_cases h : u.under (𝓞 F) = v
    · have hu : u ∈ aboveF (L := E) F v := by simp [aboveF, h]
      rw [Finset.prod_eq_single_of_mem u hu fun w _ hw => GlobalTheory.LFun.finSingle_ne (Ne.symm hw) _,
        GlobalTheory.LFun.finSingle_self]
      subst h
      rw [GlobalTheory.LFun.finSingle_self, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    · rw [GlobalTheory.LFun.finSingle_ne h, map_one]
      refine (Finset.prod_eq_one fun w hw => GlobalTheory.LFun.finSingle_ne ?_ _).symm
      rintro rfl
      exact h (by simpa [aboveF] using hw)

end Comp

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

open Formalism.L2.Host

/- English proof (translation)
Introduce `E _ _ _ ν v hv`. Establish `key : ∀ w ∈ aboveF (L` using `E) (maximalRealSubfield E) v, ν.loc w (atFin w (upF (maximalRealSubfield E) (unif v))) = ν.val w := by`. Introduce `w hw`. Take `⟨hunr, he⟩` from `hv w hw`. Use `HChar.val_eq ν hunr _ ?_` and prove the remaining obligations.

Establish `hu : w.under (𝓞 (maximalRealSubfield E)) = v` using `by simpa [aboveF] using hw`. Establish `h1` using `unif_spec v`. Unfold `IsUnifAt at h1 ⊢`. Express the relevant statement in the definitionally equal form `Valued.v (((algebraMap (maximalRealSubfield E) E ((unif v : (maximalRealSubfield E)ˣ) : maximalRealSubfield E)) : E) : w.adicCompletion E) = _`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.LFun.valuation_up hu, he, pow_one]`.

Express the relevant statement in the definitionally equal form `Valued.v (((unif v : (maximalRealSubfield E)ˣ) : maximalRealSubfield E) : v.adicCompletion (maximalRealSubfield E)) = _ at h1`. Rewrite `h1` using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Then use the resulting hypothesis. Use `show (resReal ν).1 (Neutral.B1.localIdele _ v (atFin v (unif v))) = _`. Rewrite using `[resReal_apply, ideleMap_localIdele_atFin, map_prod]`. Conclude with `Finset.prod_congr rfl key`.
-/
theorem resReal_val_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    (∀ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v,
      ν.UnrAt w ∧ w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1) →
    (GlobalTheory.PolChar.resReal ν).val v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, ν.val w := by
  intro E _ _ _ ν v hv
  have key : ∀ w ∈ aboveF (L := E) (maximalRealSubfield E) v,
      ν.loc w (atFin w (upF (maximalRealSubfield E) (unif v))) = ν.val w := by
    intro w hw
    obtain ⟨hunr, he⟩ := hv w hw
    refine HChar.val_eq ν hunr _ ?_
    have hu : w.under (𝓞 (maximalRealSubfield E)) = v := by simpa [aboveF] using hw
    have h1 := unif_spec v
    unfold IsUnifAt at h1 ⊢
    change Valued.v (((algebraMap (maximalRealSubfield E) E ((unif v : (maximalRealSubfield E)ˣ) :
      maximalRealSubfield E)) : E) : w.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.LFun.valuation_up hu, he, pow_one]
    change Valued.v (((unif v : (maximalRealSubfield E)ˣ) : maximalRealSubfield E) :
      v.adicCompletion (maximalRealSubfield E)) = _ at h1
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  show (resReal ν).1 (Neutral.B1.localIdele _ v (atFin v (unif v))) = _
  rw [resReal_apply, ideleMap_localIdele_atFin, map_prod]
  exact Finset.prod_congr rfl key

end GlobalTheory.PolChar
