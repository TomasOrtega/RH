import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal

open NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Host GlobalTheory.UnitaryBC GlobalTheory.CuspRep ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 K) K)))`.
-/
theorem continuous_infAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap K L) :=
  continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 K) K)))

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `continuous_snd.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp (Continuous.prodMk_right (0 : InfiniteAdeleRing K)))`.
-/
theorem continuous_finAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L) :=
  continuous_snd.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_right (0 : InfiniteAdeleRing K)))

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in
/- English proof (translation)
Use `show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)) (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w) (Pi.mulSingle v ((-1 : (v.Completion)ˣ) : v.Completion) (w.comap (algebraMap (maximalRealS …`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]`. Simplify using the standard rewrite rules.

Rewrite using `[Pi.mulSingle_eq_of_ne h]`. Simplify using the standard rewrite rules.
-/
theorem pInf_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) (w : InfinitePlace E) :
    pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) w =
      if w.comap (algebraMap (maximalRealSubfield E) E) = v then -1 else 1 := by
  show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w)
      (Pi.mulSingle v ((-1 : (v.Completion)ˣ) : v.Completion) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp
  · rw [Pi.mulSingle_eq_of_ne h]
    simp

/- English proof (translation)
The claim follows from `map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)`.
-/
theorem pFin_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) :
    pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) = 1 :=
  map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def iAt (v : InfinitePlace (maximalRealSubfield E)) : (Cinf E)ˣ where
  val w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then Complex.I else 1
  inv w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then -Complex.I else 1
  val_inv := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  inv_val := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp

/- English proof (translation)
Establish `h1 : pInf E (infId E (iAt v)).val = (iAt v).val`. Express the relevant statement in the definitionally equal form `(infEq E).symm (1 - infEq E 1 + infEq E (iAt v).val) = _`. Simplify using the standard rewrite rules. Establish `h2 : pFin E (infId E (iAt v)).val = 1`. Express the relevant statement in the definitionally equal form `(1 : Af E) - 0 + 0 = 1`.

Simplify using the standard rewrite rules. Establish `key : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) = infId E (iAt v) * (Units.map (conjAd E).toMonoidHom (infId E (iAt v)))⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq]`. Use `Units.ext (ad_ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `w`.

Express the relevant statement in the definitionally equal form `pInf E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val * conjAd E (infId E (iAt v)).val) w = pInf E (infId E (iAt v)).val w`. Rewrite using `[map_mul, Pi.mul_apply, GlobalTheory.ThetaPull.pInf_conjAd, h1, pInf_ideleMap_infIdele]`. Express the relevant statement in the definitionally equal form `_ * starRingEnd ℂ ((iAt v).val w) = (iAt v).val w`. Simplify using `only [iAt]`. Apply the tactic sequence `split_ifs <;> simp`.

Express the relevant statement in the definitionally equal form `pFin E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val * conjAd E (infId E (iAt v)).val) = pFin E (infId E (iAt v)).val`. Rewrite using `[map_mul, GlobalTheory.ThetaPull.pFin_conjAd, h2, pFin_ideleMap_infIdele, map_one, one_mul]`. Rewrite using `[key, map_mul, map_inv, hc, mul_inv_cancel]`.
-/
theorem apply_ideleMap_infIdele_neg_one (χ : HChar E)
    (hc : ∀ x : (AdeleRing (𝓞 E) E)ˣ, χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x)
    (v : InfinitePlace (maximalRealSubfield E)) :
    χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))) = 1 := by
  classical
  have h1 : pInf E (infId E (iAt v)).val = (iAt v).val := by
    change (infEq E).symm (1 - infEq E 1 + infEq E (iAt v).val) = _
    simp
  have h2 : pFin E (infId E (iAt v)).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have key : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) =
      infId E (iAt v) * (Units.map (conjAd E).toMonoidHom (infId E (iAt v)))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext (ad_ext ?_ ?_)
    · funext w
      change pInf E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) w = pInf E (infId E (iAt v)).val w
      rw [map_mul, Pi.mul_apply, GlobalTheory.ThetaPull.pInf_conjAd, h1, pInf_ideleMap_infIdele]
      change _ * starRingEnd ℂ ((iAt v).val w) = (iAt v).val w
      simp only [iAt]
      split_ifs <;> simp
    · change pFin E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) = pFin E (infId E (iAt v)).val
      rw [map_mul, GlobalTheory.ThetaPull.pFin_conjAd, h2,
        pFin_ideleMap_infIdele, map_one, one_mul]
  rw [key, map_mul, map_inv, hc, mul_inv_cancel]

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `e : χ * GlobalTheory.ThetaPull.thetaChar χ = 1` using `GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by`. Establish `h2` using `(GlobalTheory.ThetaPull.isAbsPow_thetaChar h).2.1 v`. Establish `h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[HChar.val_mul, Units.val_mul, h.2.1 v, h2, Units.val_one, ← Complex.cpow_add _ _ h0]`.

Simplify using the standard rewrite rules. Establish `h3` using `congrArg (fun c : HChar E => c.1 x) e`. Express the relevant statement in the definitionally equal form `χ.1 x * (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ = 1 at h3`. Conclude with `(mul_inv_eq_one.1 h3).symm`.
-/
theorem apply_conjAd_of_isAbsPow {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (x : (AdeleRing (𝓞 E) E)ˣ) :
    χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x := by
  have e : χ * GlobalTheory.ThetaPull.thetaChar χ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by
    have h2 := (GlobalTheory.ThetaPull.isAbsPow_thetaChar h).2.1 v
    have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    refine Units.ext ?_
    rw [HChar.val_mul, Units.val_mul, h.2.1 v, h2, Units.val_one, ← Complex.cpow_add _ _ h0]
    simp
  have h3 := congrArg (fun c : HChar E => c.1 x) e
  change χ.1 x * (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ = 1 at h3
  exact (mul_inv_eq_one.1 h3).symm

/- English proof (translation)
Use `letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E`. Establish `key : ∀ k : E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E (algebraMap E (AdeleRing (𝓞 E) E) k) = conjAd E (algebraMap E (AdeleRing (𝓞 E) E) k)`. Introduce `k`.

Rewrite using `[conjAd_algebraMap]`. Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap E E k`. Establish `hsymm : Continuous (infEq E).symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_infAdeleMap E E) ((continuous_infEq E).comp (continuous_star.comp hsymm)) (funext fun k => congrArg Prod.fst (key k))) x.1`.

Conclude with `congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer (continuous_finAdeleMap E E) (continuous_conjFin _) (funext fun k => congrArg Prod.snd (key k))) x.2`.
-/
theorem adeleMap_conj_eq (x : AdeleRing (𝓞 E) E) :
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra x = conjAd E x := by
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E (algebraMap E (AdeleRing (𝓞 E) E) k) =
      conjAd E (algebraMap E (AdeleRing (𝓞 E) E) k) := by
    intro k
    rw [conjAd_algebraMap]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap E E k
  have hsymm : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_infAdeleMap E E)
      ((continuous_infEq E).comp (continuous_star.comp hsymm))
      (funext fun k => congrArg Prod.fst (key k))) x.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer
      (continuous_finAdeleMap E E) (continuous_conjFin _)
      (funext fun k => congrArg Prod.snd (key k))) x.2

/- English proof (translation)
The claim follows from `Units.ext (adeleMap_conj_eq x.val)`.
-/
theorem ideleConj_eq (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x = Units.map (conjAd E).toMonoidHom x :=
  Units.ext (adeleMap_conj_eq x.val)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def resReal (χ : HChar E) : HChar (maximalRealSubfield E) :=
  ⟨χ.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E),
    χ.2.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E), fun k =>
      (congrArg χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k)).trans (χ.2.2 _)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resReal_apply (χ : HChar E) (x : (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))ˣ) :
    (resReal χ).1 x = χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) := rfl

/- English proof (translation)
The claim follows from `apply_ideleMap_infIdele_neg_one χ (apply_conjAd_of_isAbsPow h) v`.
-/
theorem resReal_locInf_neg_one {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (v : InfinitePlace (maximalRealSubfield E)) :
    (resReal χ).locInf v (-1) = 1 :=
  apply_ideleMap_infIdele_neg_one χ (apply_conjAd_of_isAbsPow h) v

end GlobalTheory.PolChar
