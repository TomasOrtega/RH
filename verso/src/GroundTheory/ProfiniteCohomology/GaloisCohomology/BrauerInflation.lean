import Mathlib
import GroundTheory.TateCohomology.InfRes
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflationDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology IntermediateField

universe u

section Surjective

variable {k Q P : Type u} [CommRing k] [Group Q] [Group P]

/- English proof (translation)
Set `S` to `f.ker`. Set `e : Q ⧸ S ≃* P` to `QuotientGroup.quotientKerEquivOfSurjective f hf`. Establish `hmem : ∀ b : B, φ.hom b ∈ Representation.invariants (A.ρ.comp S.subtype)`. Introduce `b s`. Establish `hc` using `Rep.hom_comm_apply φ (s : Q) b`.

Establish `hs : f (s : Q) = 1` using `s.2`. Express the relevant statement in the definitionally equal form `φ.hom (B.ρ (f s) b) = A.ρ s (φ.hom b) at hc`. Rewrite `hc` using `[hs, map_one, Module.End.one_apply]`. Conclude with `hc.symm`. Set `ψ : B →ₗ[k] Representation.invariants (A.ρ.comp S.subtype)` to `LinearMap.codRestrict _ φ.hom.toLinearMap hmem`.

Establish `hψ : Function.Bijective ψ`. Use `⟨fun b b' hb => hφ (congrArg Subtype.val hb), fun a => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hrange a.1 fun s hs => a.2 ⟨s, hs⟩`. Conclude with `⟨b, Subtype.ext hb⟩`. Set `e' : B.V ≃ₗ[k] (A.quotientToInvariants S).V` to `LinearEquiv.ofBijective ψ hψ`.

Establish `he : ∀ p, e'.toLinearMap ∘ₗ B.ρ p = (A.quotientToInvariants S).ρ (e.symm p) ∘ₗ e'.toLinearMap`. Introduce `p`. Take `⟨q, rfl⟩` from `hf p`. Establish `hq : e.symm (f q) = (q : Q ⧸ S)` using `(MulEquiv.symm_apply_eq e).2 rfl`. Use `LinearMap.ext fun b => Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hq]`. Conclude with `Rep.hom_comm_apply φ q b`. Set `I` to `groupCohomology.mapIso e.symm e' he 2`. Establish `hfac : groupCohomology.map f φ 2 = I.hom ≫ GroundTheory.GroupCoh.inflation A S 2`. Rewrite using `[groupCohomology.mapIso_hom, ← groupCohomology.map_comp]`.

Conclude with `groupCohomology.map_congr (MonoidHom.ext fun q => rfl) (LinearMap.ext fun b => rfl) 2`. Establish `hI : Function.Injective I.hom.hom` using `(ModuleCat.mono_iff_injective _).1 inferInstance`. Rewrite using `[hfac, ModuleCat.hom_comp, LinearMap.coe_comp]`. Conclude with `(GroundTheory.GroupCoh.inflation_two_injective (A := A) (S := S) h1).comp hI`.
-/
theorem map_two_injective_of_surjective (f : Q →* P) (hf : Function.Surjective f)
    {B : Rep.{u} k P} {A : Rep.{u} k Q} (φ : Rep.res f B ⟶ A) (hφ : Function.Injective φ.hom)
    (hrange : ∀ a : A, (∀ s ∈ f.ker, A.ρ s a = a) → ∃ b, φ.hom b = a)
    (h1 : IsZero (groupCohomology (Rep.res f.ker.subtype A) 1)) :
    Function.Injective (groupCohomology.map f φ 2).hom := by
  let S := f.ker
  let e : Q ⧸ S ≃* P := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hmem : ∀ b : B, φ.hom b ∈ Representation.invariants (A.ρ.comp S.subtype) := by
    intro b s
    have hc := Rep.hom_comm_apply φ (s : Q) b
    have hs : f (s : Q) = 1 := s.2
    change φ.hom (B.ρ (f s) b) = A.ρ s (φ.hom b) at hc
    rw [hs, map_one, Module.End.one_apply] at hc
    exact hc.symm
  let ψ : B →ₗ[k] Representation.invariants (A.ρ.comp S.subtype) :=
    LinearMap.codRestrict _ φ.hom.toLinearMap hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun b b' hb => hφ (congrArg Subtype.val hb), fun a => ?_⟩
    obtain ⟨b, hb⟩ := hrange a.1 fun s hs => a.2 ⟨s, hs⟩
    exact ⟨b, Subtype.ext hb⟩
  let e' : B.V ≃ₗ[k] (A.quotientToInvariants S).V := LinearEquiv.ofBijective ψ hψ
  have he : ∀ p, e'.toLinearMap ∘ₗ B.ρ p =
      (A.quotientToInvariants S).ρ (e.symm p) ∘ₗ e'.toLinearMap := by
    intro p
    obtain ⟨q, rfl⟩ := hf p
    have hq : e.symm (f q) = (q : Q ⧸ S) := (MulEquiv.symm_apply_eq e).2 rfl
    refine LinearMap.ext fun b => Subtype.ext ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq]
    exact Rep.hom_comm_apply φ q b
  let I := groupCohomology.mapIso e.symm e' he 2
  have hfac : groupCohomology.map f φ 2 = I.hom ≫ GroundTheory.GroupCoh.inflation A S 2 := by
    rw [groupCohomology.mapIso_hom, ← groupCohomology.map_comp]
    exact groupCohomology.map_congr (MonoidHom.ext fun q => rfl) (LinearMap.ext fun b => rfl) 2
  have hI : Function.Injective I.hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [hfac, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (GroundTheory.GroupCoh.inflation_two_injective (A := A) (S := S) h1).comp hI

end Surjective

section Tower

variable (K E F : Type u) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Normal K E]

def galTowerKerHom : Gal(F/E) →* (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E).ker where
  toFun τ := ⟨τ.restrictScalars K, MonoidHom.mem_ker.2 <| AlgEquiv.ext fun x =>
    (algebraMap E F).injective <|
      (AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) E x).trans (τ.commutes x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def galTowerKerEquiv :
    Gal(F/E) ≃* (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E).ker :=
  MulEquiv.ofBijective (galTowerKerHom K E F)
    ⟨fun τ τ' hτ => AlgEquiv.ext fun x =>
        congrArg (fun σ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E).ker => σ.1 x) hτ,
      fun σ => ⟨AlgEquiv.ofRingEquiv (f := (σ.1 : F ≃ₐ[K] F).toRingEquiv) fun x => by
          have hx := AlgEquiv.restrictNormal_commutes σ.1 E x
          have h1 : σ.1.restrictNormal E = 1 := MonoidHom.mem_ker.1 σ.2
          rw [h1] at hx
          exact hx.symm, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_galTowerKerEquiv_apply (τ : Gal(F/E)) (x : F) :
    ((galTowerKerEquiv K E F τ : Gal(F/K)) : F → F) x = τ x :=
  rfl

/- English proof (translation)
Establish `: FiniteDimensional E F` using `Module.Finite.of_restrictScalars_finite K E F`. Conclude with `(isZero_groupCohomology_one_galUnits E F).of_iso (groupCohomology.mapIso (galTowerKerEquiv K E F) (LinearEquiv.refl _ _) (fun _ => LinearMap.ext fun _ => rfl) 1).symm`.
-/
theorem isZero_groupCohomology_one_ker_galUnits [FiniteDimensional K F] :
    IsZero (groupCohomology (Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E).ker.subtype
      (galUnits.{u} K F)) 1) := by
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite K E F
  exact (isZero_groupCohomology_one_galUnits E F).of_iso
    (groupCohomology.mapIso (galTowerKerEquiv K E F) (LinearEquiv.refl _ _)
      (fun _ => LinearMap.ext fun _ => rfl) 1).symm

/- English proof (translation)
Introduce `_ _ hab` and use `Additive.toMul.injective <| Units.ext <| (algebraMap E F).injective <| congrArg (fun v : Additive Fˣ => ((Additive.toMul v : Fˣ) : F)) hab`.
-/
theorem unitsTowerHom_injective : Function.Injective (unitsTowerHom K E F).hom := fun _ _ hab =>
  Additive.toMul.injective <| Units.ext <| (algebraMap E F).injective <|
    congrArg (fun v : Additive Fˣ => ((Additive.toMul v : Fˣ) : F)) hab

/- English proof (translation)
Establish `: FiniteDimensional E F` using `Module.Finite.of_restrictScalars_finite K E F`. Establish `: IsGalois E F` using `IsGalois.tower_top_of_isGalois K E F`. Establish `hfix : ((Additive.toMul a : Fˣ) : F) ∈ Set.range (algebraMap E F)` using `(IsGalois.mem_range_algebraMap_iff_fixed _).2 fun τ => congrArg (fun v : Additive Fˣ => ((Additive.toMul v : Fˣ) : F)) (ha _ (galTowerKerEquiv K E F τ).2)`. Take `⟨x, hx⟩` from `hfix`. Establish `hx0 : x ≠ 0` using `fun h0 => (Additive.toMul a : Fˣ).ne_zero (by rw [← hx, h0, map_zero])`.

Conclude with `⟨Additive.ofMul (Units.mk0 x hx0), Additive.toMul.injective (Units.ext hx)⟩`.
-/
theorem exists_unitsTowerHom_eq [FiniteDimensional K F] [IsGalois K F] (a : Additive Fˣ)
    (ha : ∀ s ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E).ker,
      (galUnits.{u} K F).ρ s a = a) :
    ∃ b, (unitsTowerHom K E F).hom b = a := by
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite K E F
  have : IsGalois E F := IsGalois.tower_top_of_isGalois K E F
  have hfix : ((Additive.toMul a : Fˣ) : F) ∈ Set.range (algebraMap E F) :=
    (IsGalois.mem_range_algebraMap_iff_fixed _).2 fun τ =>
      congrArg (fun v : Additive Fˣ => ((Additive.toMul v : Fˣ) : F))
        (ha _ (galTowerKerEquiv K E F τ).2)
  obtain ⟨x, hx⟩ := hfix
  have hx0 : x ≠ 0 := fun h0 => (Additive.toMul a : Fˣ).ne_zero (by rw [← hx, h0, map_zero])
  exact ⟨Additive.ofMul (Units.mk0 x hx0), Additive.toMul.injective (Units.ext hx)⟩

/- English proof (translation)
The claim follows from `map_two_injective_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) F) (unitsTowerHom K E F) (unitsTowerHom_injective K E F) (exists_unitsTowerHom_eq K E F) (isZero_groupCohomology_one_ker_galUnits K E F)`.
-/
theorem unitsInflationTower_two_injective [FiniteDimensional K F] [IsGalois K F] :
    Function.Injective (unitsInflationTower K E F 2).hom :=
  map_two_injective_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) F)
    (unitsTowerHom K E F) (unitsTowerHom_injective K E F) (exists_unitsTowerHom_eq K E F)
    (isZero_groupCohomology_one_ker_galUnits K E F)

end Tower

section LE

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
  (h : E ≤ F)

/- English proof (translation)
Set `: Algebra E F` to `(IntermediateField.inclusion h).toRingHom.toAlgebra`. Establish `: IsScalarTower K E F` using `IsScalarTower.of_algebraMap_eq' rfl`. Conclude with `unitsInflationTower_two_injective K E F`.
-/
theorem unitsInflationOfLE_two_injective [Normal K E] [FiniteDimensional K F] [IsGalois K F] :
    Function.Injective (unitsInflationOfLE h 2).hom := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact unitsInflationTower_two_injective K E F

/- English proof (translation)
The claim follows from `AlgEquiv.ext fun x => Subtype.ext <| (coe_galRestrictOfLE_apply h _ x).trans <| (AlgEquiv.restrictNormal_commutes σ F (IntermediateField.inclusion h x)).trans (AlgEquiv.restrictNormal_commutes σ E x).symm`.
-/
theorem galRestrictOfLE_restrictNormalHom [Normal K E] [Normal K F] (σ : Gal(L/K)) :
    galRestrictOfLE h (AlgEquiv.restrictNormalHom F σ) = AlgEquiv.restrictNormalHom E σ :=
  AlgEquiv.ext fun x => Subtype.ext <| (coe_galRestrictOfLE_apply h _ x).trans <|
    (AlgEquiv.restrictNormal_commutes σ F (IntermediateField.inclusion h x)).trans
      (AlgEquiv.restrictNormal_commutes σ E x).symm

variable [IsGalois K L]

/- English proof (translation)
Use extensionality with `n : 1`. Rewrite using `[← cancel_mono ((cochainsComplexι (galUnits.{u} K L)).f n), HomologicalComplex.comp_f, Category.assoc]`. Use extensionality with `x : 2`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `(unitsRestrictHom F).hom ((unitsOfLE h).hom (x fun i => galRestrictOfLE h (AlgEquiv.restrictNormalHom F (g i)))) = (unitsRestrictHom E).hom (x fun i => AlgEquiv.restrictNormalHom E (g i))`.

Simplify using `only [galRestrictOfLE_restrictNormalHom]`. Conclude with `Additive.toMul.injective (Units.ext rfl)`.
-/
theorem cochainsMap_galRestrictOfLE_comp_unitsInflationCochains [FiniteDimensional K E]
    [Normal K E] [FiniteDimensional K F] [Normal K F] :
    groupCohomology.cochainsMap (galRestrictOfLE h) (unitsOfLE h) ≫ unitsInflationCochains F =
      unitsInflationCochains E := by
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K L)).f n), HomologicalComplex.comp_f,
    Category.assoc]
  ext x : 2
  funext g
  change (unitsRestrictHom F).hom ((unitsOfLE h).hom
      (x fun i => galRestrictOfLE h (AlgEquiv.restrictNormalHom F (g i)))) =
    (unitsRestrictHom E).hom (x fun i => AlgEquiv.restrictNormalHom E (g i))
  simp only [galRestrictOfLE_restrictNormalHom]
  exact Additive.toMul.injective (Units.ext rfl)

/- English proof (translation)
Unfold `unitsInflationOfLE unitsInflation groupCohomology.map`. Use `(HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_` and prove the remaining obligations. Rewrite using `[cochainsMap_galRestrictOfLE_comp_unitsInflationCochains]`.
-/
theorem unitsInflationOfLE_comp_unitsInflation [FiniteDimensional K E] [Normal K E]
    [FiniteDimensional K F] [Normal K F] (n : ℕ) :
    unitsInflationOfLE h n ≫ unitsInflation F n = unitsInflation E n := by
  unfold unitsInflationOfLE unitsInflation groupCohomology.map
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [cochainsMap_galRestrictOfLE_comp_unitsInflationCochains]

end LE

section Profinite

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in

/- English proof (translation)
Introduce `_ hx` and use `(mem_fixedField_iff _ _).2 fun σ hσ => (mem_fixedField_iff _ _).1 hx σ (h hσ)`.
-/
theorem fixedField_le_of_le {U V : OpenNormalSubgroup Gal(L/K)} (h : V ≤ U) :
    fixedField (U : Subgroup Gal(L/K)) ≤ fixedField (V : Subgroup Gal(L/K)) :=
  fun _ hx => (mem_fixedField_iff _ _).2 fun σ hσ => (mem_fixedField_iff _ _).1 hx σ (h hσ)

/- English proof (translation)
Rewrite using `[groupCohomologyQuotientGalUnitsIso, groupCohomologyQuotientGalUnitsIso, groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]`. Unfold `transition unitsInflationOfLE`. Rewrite using `[← groupCohomology.map_comp, ← groupCohomology.map_comp]`. Use `groupCohomology.map_congr ?_ ?_ n` and prove the remaining obligations. Use `ext1 σ`.

Take `⟨q, rfl⟩` from `(quotientEquivGal V).surjective σ`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H g`. Express the relevant statement in the definitionally equal form `quotientMapOfLE h ((quotientEquivGal V).symm (quotientEquivGal V (g : Gal(L/K) ⧸ (V : Subgroup Gal(L/K))))) = (quotientEquivGal U).symm (galRestrictOfLE (fixedField_le_of_le h) (quotientEquivGal V (g : Gal(L/K) ⧸ (V : Subgroup Gal(L/K)))))`. Rewrite using `[MulEquiv.symm_apply_apply, quotientMapOfLE_mk, eq_comm, MulEquiv.symm_apply_eq, quotientEquivGal_mk_eq_restrictNormalHom, quotientEquivGal_mk_eq_restrictNormalHom, galRestrictOfLE_restrictNormalHom]`.

Conclude with `LinearMap.ext fun x => Additive.toMul.injective (Units.ext rfl)`.
-/
theorem transition_comp_groupCohomologyQuotientGalUnitsIso {U V : OpenNormalSubgroup Gal(L/K)}
    (h : V ≤ U) (n : ℕ) :
    transition (galUnits.{u} K L) h n ≫ (groupCohomologyQuotientGalUnitsIso V n).hom =
      (groupCohomologyQuotientGalUnitsIso U n).hom ≫
        unitsInflationOfLE (fixedField_le_of_le h) n := by
  rw [groupCohomologyQuotientGalUnitsIso, groupCohomologyQuotientGalUnitsIso,
    groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
  unfold transition unitsInflationOfLE
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext1 σ
    obtain ⟨q, rfl⟩ := (quotientEquivGal V).surjective σ
    induction q using QuotientGroup.induction_on with
    | H g =>
      change quotientMapOfLE h ((quotientEquivGal V).symm
          (quotientEquivGal V (g : Gal(L/K) ⧸ (V : Subgroup Gal(L/K))))) =
        (quotientEquivGal U).symm (galRestrictOfLE (fixedField_le_of_le h)
          (quotientEquivGal V (g : Gal(L/K) ⧸ (V : Subgroup Gal(L/K)))))
      rw [MulEquiv.symm_apply_apply, quotientMapOfLE_mk, eq_comm, MulEquiv.symm_apply_eq,
        quotientEquivGal_mk_eq_restrictNormalHom,
        quotientEquivGal_mk_eq_restrictNormalHom, galRestrictOfLE_restrictNormalHom]
  · exact LinearMap.ext fun x => Additive.toMul.injective (Units.ext rfl)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨y₀, rfl⟩ : ∃ y₀, (groupCohomologyQuotientGalUnitsIso U 2).hom.hom y₀ = y` from `⟨(groupCohomologyQuotientGalUnitsIso U 2).inv.hom y, by`. Rewrite using `[← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply]⟩`. Establish `hinf : (inflation (galUnits.{u} K L) U 2).hom y₀ = 0`.

Rewrite using `[inflation_galUnits_eq, ModuleCat.hom_comp, LinearMap.comp_apply]`. Conclude with `hy`. Take `⟨V, hVU, hV⟩` from `exists_transition_eq_zero (galUnits.{u} K L) 2 U y₀ hinf`. Establish `hsq` using `congrArg (fun φ => φ.hom y₀) (transition_comp_groupCohomologyQuotientGalUnitsIso hVU 2)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply, hV, map_zero] at hsq`.

Conclude with `unitsInflationOfLE_two_injective (fixedField_le_of_le hVU) (hsq.symm.trans (map_zero _).symm)`.
-/
theorem unitsInflation_fixedField_two_injective (U : OpenNormalSubgroup Gal(L/K)) :
    Function.Injective (unitsInflation (fixedField (U : Subgroup Gal(L/K))) 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨y₀, rfl⟩ : ∃ y₀, (groupCohomologyQuotientGalUnitsIso U 2).hom.hom y₀ = y :=
    ⟨(groupCohomologyQuotientGalUnitsIso U 2).inv.hom y, by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
        LinearMap.id_apply]⟩
  have hinf : (inflation (galUnits.{u} K L) U 2).hom y₀ = 0 := by
    rw [inflation_galUnits_eq, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hy
  obtain ⟨V, hVU, hV⟩ := exists_transition_eq_zero (galUnits.{u} K L) 2 U y₀ hinf
  have hsq := congrArg (fun φ => φ.hom y₀)
    (transition_comp_groupCohomologyQuotientGalUnitsIso hVU 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hV, map_zero] at hsq
  exact unitsInflationOfLE_two_injective (fixedField_le_of_le hVU)
    (hsq.symm.trans (map_zero _).symm)

/- English proof (translation)
Substitute `hEF` using the available equality. Conclude with `hE`.
-/
theorem unitsInflation_two_injective_of_eq {E F : IntermediateField K L} [FiniteDimensional K E]
    [Normal K E] [FiniteDimensional K F] [Normal K F] (hEF : E = F)
    (hE : Function.Injective (unitsInflation E 2).hom) :
    Function.Injective (unitsInflation F 2).hom := by
  subst hEF
  exact hE

/- English proof (translation)
Establish `: Algebra.IsSeparable K E` using `Algebra.isSeparable_tower_bot_of_isSeparable K E L`. Establish `: IsGalois K E` using `⟨⟩`. Set `E' : FiniteGaloisIntermediateField K L` to `{ toIntermediateField := E }`. Conclude with `unitsInflation_two_injective_of_eq (congrArg FiniteGaloisIntermediateField.toIntermediateField (fixedFiniteGalois_fixingOpenNormalSubgroup E')) (unitsInflation_fixedField_two_injective (fixingOpenNormalSubgroup E'))`.
-/
theorem brauerInflation_injective (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] : Function.Injective (brauerInflation E).hom := by
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  have : IsGalois K E := ⟨⟩
  let E' : FiniteGaloisIntermediateField K L := { toIntermediateField := E }
  exact unitsInflation_two_injective_of_eq
    (congrArg FiniteGaloisIntermediateField.toIntermediateField
      (fixedFiniteGalois_fixingOpenNormalSubgroup E'))
    (unitsInflation_fixedField_two_injective (fixingOpenNormalSubgroup E'))

end Profinite

end GroundTheory.ProfCoh
