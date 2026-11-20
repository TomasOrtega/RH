import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CircleHomEqZpow
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuInfType

/- English proof (translation)
Establish `hmem : ∀ z, (χ (Circle.toUnits z) : ℂ) ∈ Submonoid.unitSphere ℂ` using `fun z => by`. Simplify `hu _` using `[Submonoid.unitSphere, mem_sphere_zero_iff_norm]`. Set `f : Circle →* Circle` to `{ toFun := fun z => (⟨(χ (Circle.toUnits z) : ℂ), hmem z⟩ : Circle) map_one' := Circle.ext (by simp) map_mul' := fun a b => Circle.ext (by`. Express the relevant statement in the definitionally equal form `((χ (Circle.toUnits (a * b))) : ℂ) = (χ (Circle.toUnits a) : ℂ) * (χ (Circle.toUnits b) : ℂ)`. Rewrite using `[map_mul, map_mul, Units.val_mul]) }`.

Establish `hcu : Continuous (Circle.toUnits : Circle → ℂˣ)`. Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val`. Establish `: (fun x : Circle => ((Circle.toUnits x)⁻¹ : ℂˣ).val) = fun x : Circle => (x : ℂ)⁻¹`.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `(continuous_subtype_val).inv₀ fun x => Circle.coe_ne_zero x`. Establish `hf : Continuous f`.

Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (hc.comp hcu)`. Take `⟨n, hn⟩` from `GlobalTheory.circle_hom_eq_zpow f hf`. Use `⟨n, fun z => ?_⟩` and prove the remaining obligations. Establish `hz0 : (z : ℂ) ≠ 0` using `z.ne_zero`.

Establish `hn0 : (‖(z : ℂ)‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz0`. Establish `hw : (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Submonoid.unitSphere ℂ`. Simplify using `[Submonoid.unitSphere, mem_sphere_zero_iff_norm, norm_div, hz0]`. Set `w : Circle` to `(⟨_, hw⟩ : Circle)`. Set `r : ℂˣ` to `Units.mk0 (‖(z : ℂ)‖ : ℂ) hn0`.

Establish `hzr : z = Circle.toUnits w * r` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) * (‖(z : ℂ)‖ : ℂ)`. Use the proof step `field_simp)`. Establish `hr : χ r = 1` using `hp r (by simp [r])`. Establish `h1` using `congrArg (fun c : Circle => (c : ℂ)) (hn w)`.

Establish `hχ : χ z = χ (Circle.toUnits w)` using `by rw [hzr, map_mul, hr, mul_one]`. Rewrite using `[hχ]`. Express the relevant statement in the definitionally equal form `((f w : Circle) : ℂ) = _`. Rewrite using `[h1, Circle.coe_zpow]`.
-/
theorem char_eq_zpow (χ : ℂˣ →* ℂˣ) (hc : Continuous χ) (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hp : ∀ z : ℂˣ, (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χ z = 1) :
    ∃ n : ℤ, ∀ z : ℂˣ, (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n := by
  have hmem : ∀ z, (χ (Circle.toUnits z) : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hu _
  let f : Circle →* Circle :=
    { toFun := fun z => (⟨(χ (Circle.toUnits z) : ℂ), hmem z⟩ : Circle)
      map_one' := Circle.ext (by simp)
      map_mul' := fun a b => Circle.ext (by
        change ((χ (Circle.toUnits (a * b))) : ℂ) = (χ (Circle.toUnits a) : ℂ) * (χ (Circle.toUnits b) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcu : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · exact continuous_subtype_val
    · have : (fun x : Circle => ((Circle.toUnits x)⁻¹ : ℂˣ).val) = fun x : Circle => (x : ℂ)⁻¹ := by
        funext x; simp
      rw [this]
      exact (continuous_subtype_val).inv₀ fun x => Circle.coe_ne_zero x
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.comp (hc.comp hcu)
  obtain ⟨n, hn⟩ := GlobalTheory.circle_hom_eq_zpow f hf
  refine ⟨n, fun z => ?_⟩
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hn0 : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hw : (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere, mem_sphere_zero_iff_norm, norm_div, hz0]
  let w : Circle := (⟨_, hw⟩ : Circle)
  let r : ℂˣ := Units.mk0 (‖(z : ℂ)‖ : ℂ) hn0
  have hzr : z = Circle.toUnits w * r := Units.ext (by
    change (z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) * (‖(z : ℂ)‖ : ℂ)
    field_simp)
  have hr : χ r = 1 := hp r (by simp [r])
  have h1 := congrArg (fun c : Circle => (c : ℂ)) (hn w)
  have hχ : χ z = χ (Circle.toUnits w) := by rw [hzr, map_mul, hr, mul_one]
  rw [hχ]
  change ((f w : Circle) : ℂ) = _
  rw [h1, Circle.coe_zpow]

end GlobalTheory.MuInfType

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def single (v : InfinitePlace E) : ℂˣ →* (Cinf E)ˣ := Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℂ) v)

/- English proof (translation)
The claim follows from `Continuous.units_map _ (by show Continuous (fun z : ℂ => (Pi.mulSingle v z : InfinitePlace E → ℂ)) exact continuous_mulSingle (A := fun _ : InfinitePlace E => ℂ) v)`.
-/
theorem continuous_single (v : InfinitePlace E) : Continuous (single v) :=
  Continuous.units_map _ (by
    show Continuous (fun z : ℂ => (Pi.mulSingle v z : InfinitePlace E → ℂ))
    exact continuous_mulSingle (A := fun _ : InfinitePlace E => ℂ) v)

variable (E) in

abbrev below (v : InfinitePlace E) : InfinitePlace (maximalRealSubfield E) := v.comap (algebraMap (maximalRealSubfield E) E)

def iota (v : InfinitePlace E) : (below E v).Completion →+* ℂ :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).toRingHom.comp
    (LiesOver.completionMap (v := below E v) (w := v))

/- English proof (translation)
Use `Units.ext (ad_ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Establish `h1 : ∀ u : (Cinf E)ˣ, pInf E (infId E u).val = u.val` using `fun u => by`. Express the relevant statement in the definitionally equal form `(infEq E).symm (1 - infEq E 1 + infEq E u.val) = _`. Simplify using the standard rewrite rules.

Rewrite using `[h1]`. Use `show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)) (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w) (Pi.mulSingle (below E v) ((x : (below E v).Completion)) (w.comap (algebraMap (maximalReal …`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]`.

Simplify using `[single, iota]`. Establish `h' : w.comap (algebraMap (maximalRealSubfield E) E) ≠ below E v` using `fun e => h ((IsCMField.equivInfinitePlace E).injective e)`. Rewrite using `[Pi.mulSingle_eq_of_ne h']`. Simplify using `[single, Pi.mulSingle_eq_of_ne h]`. Express the relevant statement in the definitionally equal form `pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) : Ad E) = pFin E (infId E _).val`.

Use `(map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Af E) = 1 - 0 + 0`. Simplify using the standard rewrite rules.
-/
theorem ideleMap_infIdele (v : InfinitePlace E) (x : ((below E v).Completion)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) =
      infId E (single v (Units.map (iota v).toMonoidHom x)) := by
  classical
  refine Units.ext (ad_ext ?_ ?_)
  · funext w
    have h1 : ∀ u : (Cinf E)ˣ, pInf E (infId E u).val = u.val := fun u => by
      change (infEq E).symm (1 - infEq E 1 + infEq E u.val) = _
      simp
    rw [h1]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
      (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w)
        (Pi.mulSingle (below E v) ((x : (below E v).Completion)) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same]
      simp [single, iota]
    · have h' : w.comap (algebraMap (maximalRealSubfield E) E) ≠ below E v := fun e =>
        h ((IsCMField.equivInfinitePlace E).injective e)
      rw [Pi.mulSingle_eq_of_ne h']
      simp [single, Pi.mulSingle_eq_of_ne h]
  · change pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) : Ad E) =
      pFin E (infId E _).val
    refine (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)).trans ?_
    change (1 : Af E) = 1 - 0 + 0
    simp

/- English proof (translation)
Set `ψ : ℝ →+* ℂ` to `(iota v).comp (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.toRingHom`. Establish `hψ : Continuous ψ` using `((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp (LiesOver.continuous_completionMap (v := below E v) (w := v))).comp (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.continuous`. Use `map_real_smul ψ hψ s 1` as an intermediate fact. Simplify `this` using `[ψ]`.
-/
theorem iota_real (v : InfinitePlace E) (s : ℝ) :
    iota v ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s) = s := by
  let ψ : ℝ →+* ℂ := (iota v).comp
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.toRingHom
  have hψ : Continuous ψ :=
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      (LiesOver.continuous_completionMap (v := below E v) (w := v))).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.continuous
  have := map_real_smul ψ hψ s 1
  simpa [ψ] using this

end GlobalTheory.MuInfType

end

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

/- English proof (translation)
Introduce `E _ _ _ μ hU hη`. Set `χv : InfinitePlace E → ℂˣ →* ℂˣ` to `fun v => (chiInf μ).comp (single v)`. Establish `hcont : ∀ v, Continuous (χv v)` using `fun v => (continuous_chiInf μ).comp (continuous_single v)`. Establish `hunit : ∀ v z, ‖(χv v z : ℂ)‖ = 1` using `fun v z => hU _`. Establish `hval : ∀ v (x : ((below E v).Completion)ˣ), χv v (Units.map (iota v).toMonoidHom x) = (GlobalTheory.GalOfCusp.quadChar E).1 (infIdele _ (below E v) x)`.

Introduce `v x`. Express the relevant statement in the definitionally equal form `μ.1 (infId E (single v _)) = _`. Rewrite using `[← ideleMap_infIdele, hη]`. Establish `hneg : ∀ v, χv v (-1) = -1`. Introduce `v`.

Establish `e : Units.map (iota v).toMonoidHom (-1) = -1` using `Units.ext (by simp)`. Establish `h` using `hval v (-1)`. Rewrite `h` using `[e]`. Rewrite using `[h]`. Conclude with `GlobalTheory.GalOfCusp.quadChar_locInf E (below E v)`.

Establish `hpos : ∀ v (z : ℂˣ), (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χv v z = 1`. Introduce `v z hz`. Use `set s : ℝ := Real.sqrt ‖(z : ℂ)‖ with hs`. Establish `hs0 : s ≠ 0`. Rewrite using `[hs]`.

Conclude with `(Real.sqrt_pos.2 (norm_pos_iff.2 z.ne_zero)).ne'`. Establish `hx0 : (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s ≠ 0`. Simplify using `using hs0`. Set `x : ((below E v).Completion)ˣ` to `Units.mk0 _ hx0`. Establish `hx : Units.map (iota v).toMonoidHom x ^ 2 = z` using `Units.ext (by`.

Simplify using `only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, x, Units.val_mk0, iota_real]`. Rewrite using `[← Complex.ofReal_pow, hs, Real.sq_sqrt (norm_nonneg _), hz])`. Rewrite using `[← hx, map_pow, hval]`. Express the relevant statement in the definitionally equal form `(Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E _)) ^ 2 = 1`. Rewrite using `[← map_pow, Int.units_sq, map_one]`.

Use `choose e he using fun v => GlobalTheory.MuInfType.char_eq_zpow (χv v) (hcont v) (hunit v) (hpos v)`. Use `⟨e, fun v => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `h` using `he v (-1)`. Rewrite `h` using `[hneg]`. Simplify using `only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, div_one] at h`.

Break down `Int.even_or_odd (e v) with h' | h'` into its components or cases. Rewrite `h` using `[h'.neg_one_zpow]`. Evaluate the numerical expressions using `at h`. Conclude with `h'`. Set `zv : InfinitePlace E → ℂˣ` to `fun v => Units.map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) v) z`.

Establish `hz : z = ∏ v, single v (zv v)` using `Units.ext (by`. Rewrite using `[Units.coe_prod]`. Simplify using `only [single, zv, Units.coe_map, MonoidHom.coe_coe, MonoidHom.mulSingle_apply, Pi.evalMonoidHom_apply]`. Conclude with `(Finset.univ_prod_mulSingle z.val).symm)`. Use `conv_lhs => rw [hz]`.

Rewrite using `[map_prod, Units.coe_prod]`. Conclude with `Finset.prod_congr rfl fun v _ => he v (zv v)`.
-/
theorem infType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ∃ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ hU hη
  let χv : InfinitePlace E → ℂˣ →* ℂˣ := fun v => (chiInf μ).comp (single v)
  have hcont : ∀ v, Continuous (χv v) := fun v => (continuous_chiInf μ).comp (continuous_single v)
  have hunit : ∀ v z, ‖(χv v z : ℂ)‖ = 1 := fun v z => hU _
  have hval : ∀ v (x : ((below E v).Completion)ˣ),
      χv v (Units.map (iota v).toMonoidHom x) = (GlobalTheory.GalOfCusp.quadChar E).1 (infIdele _ (below E v) x) := by
    intro v x
    change μ.1 (infId E (single v _)) = _
    rw [← ideleMap_infIdele, hη]
  have hneg : ∀ v, χv v (-1) = -1 := by
    intro v
    have e : Units.map (iota v).toMonoidHom (-1) = -1 := Units.ext (by simp)
    have h := hval v (-1)
    rw [e] at h
    rw [h]
    exact GlobalTheory.GalOfCusp.quadChar_locInf E (below E v)
  have hpos : ∀ v (z : ℂˣ), (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χv v z = 1 := by
    intro v z hz
    set s : ℝ := Real.sqrt ‖(z : ℂ)‖ with hs
    have hs0 : s ≠ 0 := by
      rw [hs]
      exact (Real.sqrt_pos.2 (norm_pos_iff.2 z.ne_zero)).ne'
    have hx0 : (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s ≠ 0 := by
      simpa using hs0
    let x : ((below E v).Completion)ˣ := Units.mk0 _ hx0
    have hx : Units.map (iota v).toMonoidHom x ^ 2 = z := Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, x,
        Units.val_mk0, iota_real]
      rw [← Complex.ofReal_pow, hs, Real.sq_sqrt (norm_nonneg _), hz])
    rw [← hx, map_pow, hval]
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E _)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  choose e he using fun v => GlobalTheory.MuInfType.char_eq_zpow (χv v) (hcont v) (hunit v) (hpos v)
  refine ⟨e, fun v => ?_, fun z => ?_⟩
  · have h := he v (-1)
    rw [hneg] at h
    simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, div_one] at h
    rcases Int.even_or_odd (e v) with h' | h'
    · rw [h'.neg_one_zpow] at h
      norm_num at h
    · exact h'
  · let zv : InfinitePlace E → ℂˣ := fun v => Units.map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) v) z
    have hz : z = ∏ v, single v (zv v) := Units.ext (by
      rw [Units.coe_prod]
      simp only [single, zv, Units.coe_map, MonoidHom.coe_coe, MonoidHom.mulSingle_apply, Pi.evalMonoidHom_apply]
      exact (Finset.univ_prod_mulSingle z.val).symm)
    conv_lhs => rw [hz]
    rw [map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl fun v _ => he v (zv v)

end GlobalTheory.MuInfType

end
