import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace RootFieldNumerics

section General

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

/- English proof (translation)
Establish `h1` using `Spec.map_comp (X.presheaf.stalkSpecializes p.2) (Scheme.stalkClosedPointTo ξ)`. Establish `h2` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) p.2`. Conclude with `(congrArg (· ≫ X.fromSpecStalk p.1) h1).trans <| (Category.assoc _ _ _).trans <| (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h2).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)`.
-/
theorem spMap_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  have h1 := Spec.map_comp (X.presheaf.stalkSpecializes p.2) (Scheme.stalkClosedPointTo ξ)
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) p.2
  exact (congrArg (· ≫ X.fromSpecStalk p.1) h1).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h2).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

/- English proof (translation)
Establish `hF : IsField (X.presheaf.stalk (genPt ξ))` using `(RingEquiv.ofBijective _ hb).toMulEquiv.isField (Field.toIsField Ω)`. Establish `h1 : x' ∈ Set.range (X.fromSpecStalk (genPt ξ))`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `h`. Establish `h2 : genPt ξ ∈ Set.range (X.fromSpecStalk (genPt ξ))`.

Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `specializes_rfl`. Take `⟨u, hu⟩` from `h1`. Take `⟨v, hv⟩` from `h2`. Set `_` to `hF.toField`.

Establish `huv : u = v` using `Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) u v`. Rewrite using `[← hu, huv, hv]`.
-/
theorem eq_of_specializes_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (x' : X) (h : x' ⤳ genPt ξ) : x' = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ hb).toMulEquiv.isField (Field.toIsField Ω)
  have h1 : x' ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact h
  have h2 : genPt ξ ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  let _ := hF.toField
  have huv : u = v := Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) u v
  rw [← hu, huv, hv]

/- English proof (translation)
Set `e` to `RingEquiv.ofBijective _ hb`. Use `⟨(genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom, ?_⟩` and prove the remaining obligations. Establish `h1 : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) = CommRingCat.ofHom (genMap ξ' ⟨genPt ξ, h⟩)`. Use extensionality with `a`. Conclude with `congrArg (genMap ξ' ⟨genPt ξ, h⟩) (e.symm_apply_apply a)`.

Establish `h2` using `spMap_genMap ξ' ⟨genPt ξ, h⟩`. Establish `h3` using `Spec.map_comp (Scheme.stalkClosedPointTo ξ) (CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom))`. Use `h2.symm.trans ?_` and prove the remaining obligations. Use `(congrArg (fun u => Spec.map u ≫ X.fromSpecStalk (genPt ξ)) h1.symm).trans ?_` and prove the remaining obligations. Use `(congrArg (· ≫ X.fromSpecStalk (genPt ξ)) h3).trans <| (Category.assoc _ _ _).trans ?_` and prove the remaining obligations.

Conclude with `congrArg (spMap ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)`.
-/
theorem exists_factor {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (ξ' : Spec (CommRingCat.of Ω') ⟶ X)
    (h : genPt ξ' ⤳ genPt ξ) : ∃ φ : Ω →+* Ω', ξ' = spMap φ ≫ ξ := by
  let e := RingEquiv.ofBijective _ hb
  refine ⟨(genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom, ?_⟩
  have h1 : Scheme.stalkClosedPointTo ξ ≫
      CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) =
      CommRingCat.ofHom (genMap ξ' ⟨genPt ξ, h⟩) := by
    ext a
    exact congrArg (genMap ξ' ⟨genPt ξ, h⟩) (e.symm_apply_apply a)
  have h2 := spMap_genMap ξ' ⟨genPt ξ, h⟩
  have h3 := Spec.map_comp (Scheme.stalkClosedPointTo ξ)
    (CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom))
  refine h2.symm.trans ?_
  refine (congrArg (fun u => Spec.map u ≫ X.fromSpecStalk (genPt ξ)) h1.symm).trans ?_
  refine (congrArg (· ≫ X.fromSpecStalk (genPt ξ)) h3).trans <| (Category.assoc _ _ _).trans ?_
  exact congrArg (spMap ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) ≫ ·)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Introduce `Ω _ ξ cst hξ hs a ha`. Establish `: NumberField c.F` using `{ to_charZero := inferInstance, to_finiteDimensional := c.fin }`. Take `⟨b, hb⟩` from `o.comp_onto (genPt ξ) (eq_of_specializes_genPt hξ.bij)`. Take `⟨φ, hφ⟩` from `exists_factor hξ.bij (o.Fx b).ξf (hb ▸ specializes_rfl)`. Set `r` to `o.Or 0 b`.

Establish `h1 : spMap (r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) = spMap ((r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F))`. Rewrite using `[← r.𝔐.cst_over, ← Category.assoc, r.g_over, hφ, Category.assoc, Category.assoc, hs, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `h2 : r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) = (r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F)` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Establish `h3 : r.𝔐.cst = r.g.comp (φ.comp cst)` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2`.

Take `⟨x, hx⟩` from `r.g_const (φ a) (ha.algHom φ.toIntAlgHom)`. Rewrite `hx` using `[h3]`. Conclude with `⟨x, φ.injective (r.g.injective hx)⟩`.
-/
theorem splitComps_of_origin {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨b, hb⟩ := o.comp_onto (genPt ξ) (eq_of_specializes_genPt hξ.bij)
  obtain ⟨φ, hφ⟩ := exists_factor hξ.bij (o.Fx b).ξf (hb ▸ specializes_rfl)
  let r := o.Or 0 b
  have h1 : spMap (r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) =
      spMap ((r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← r.𝔐.cst_over, ← Category.assoc, r.g_over, hφ, Category.assoc, Category.assoc, hs,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have h2 : r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) =
      (r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : r.𝔐.cst = r.g.comp (φ.comp cst) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  obtain ⟨x, hx⟩ := r.g_const (φ a) (ha.algHom φ.toIntAlgHom)
  rw [h3] at hx
  exact ⟨x, φ.injective (r.g.injective hx)⟩

end RootFieldNumerics
