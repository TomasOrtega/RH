import Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
import Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
import Development.EtaleCohomology.EtaleSheaves.CurveKrullDimTopology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

def LeafCurveNotPoint : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsCurve c → ¬ Subsingleton C

/- English proof (translation)
Set `e : (⊥ : Subalgebra Ω Ω) ≃+* Ω` to `(Algebra.botEquiv Ω Ω).toRingEquiv`. Set `φ : Sp Ω ⟶ Sp (⊥ : Subalgebra Ω Ω)` to `Spec.map e.toCommRingCatIso.hom`. Establish `: IsIso φ` using `inferInstance`. Establish `: SmoothOfRelativeDimension 1 (c ≫ φ)` using `inferInstanceAs (SmoothOfRelativeDimension (1 + 0) (c ≫ φ))`. Establish `h` using `hD Ω Ω (⊥ : Subalgebra Ω Ω) Subalgebra.fg_bot (c ≫ φ) this`.

Rewrite `h` using `[ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field, zero_add]`. Then use the resulting hypothesis.
-/
theorem dim_le_one (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) {Ω : Type} [Field Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : SmoothOfRelativeDimension 1 c) : topologicalKrullDim C ≤ 1 := by
  let e : (⊥ : Subalgebra Ω Ω) ≃+* Ω := (Algebra.botEquiv Ω Ω).toRingEquiv
  let φ : Sp Ω ⟶ Sp (⊥ : Subalgebra Ω Ω) := Spec.map e.toCommRingCatIso.hom
  have : IsIso φ := inferInstance
  have : SmoothOfRelativeDimension 1 (c ≫ φ) := inferInstanceAs (SmoothOfRelativeDimension (1 + 0) (c ≫ φ))
  have h := hD Ω Ω (⊥ : Subalgebra Ω Ω) Subalgebra.fg_bot (c ≫ φ) this
  rwa [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field, zero_add] at h

/- English proof (translation)
Introduce `Ω _ _ C c hc`. Take `⟨hI, hPr, hS⟩` from `id hc`. Establish `: LocallyOfFiniteType c` using `inferInstance`. Establish `: IsLocallyNoetherian C` using `LocallyOfFiniteType.isLocallyNoetherian c`. Establish `: CompactSpace C`.

Establish `: QuasiCompact c` using `inferInstance`. Conclude with `(quasiCompact_iff_compactSpace c).mp this`. Establish `: IsNoetherian C` using `by constructor`. Establish `: NoetherianSpace C` using `inferInstance`. Establish `: JacobsonSpace C` using `LocallyOfFiniteType.jacobsonSpace c`.

Establish `hd` using `dim_le_one hD c hS`. Use `⟨fun hfin => hP Ω c hc ?_, fun Z hZ hinf => ?_⟩` and prove the remaining obligations. Establish `hcp : closedPoints C = univ`. Establish `: IsClosed (closedPoints C)`. Establish `: closedPoints C = ⋃ x ∈ (hfin.subset (subset_univ (closedPoints C))).toFinset, {x}` using `by ext; simp`.

Rewrite using `[this]; exact isClosed_biUnion_finset fun x hx => by simpa using hx`. Rewrite using `[← this.closure_eq]`. Conclude with `closure_closedPoints`. Establish `hη : IsClosed ({genericPoint C} : Set C)`. Rewrite using `[← mem_closedPoints_iff, hcp]`.

Discharge the goal by the elementary cases of `trivial`. Establish `: ({genericPoint C} : Set C) = univ`. Rewrite using `[← hη.closure_eq]`. Conclude with `(genericPoint_spec C).def`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations.

Establish `ha : a ∈ ({genericPoint C} : Set C)` using `this ▸ mem_univ a`. Establish `hb : b ∈ ({genericPoint C} : Set C)` using `this ▸ mem_univ b`. Conclude with `ha.trans hb.symm`. Assume the negation of the conclusion as `hne`. Conclude with `hinf (finite_of_closed hd Z hZ hne)`.
-/
theorem LeafCurveSmall_of_cut (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) (hP : LeafCurveNotPoint) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall := by
  intro Ω _ _ C c hc
  obtain ⟨hI, hPr, hS⟩ := id hc
  have : LocallyOfFiniteType c := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : CompactSpace C := by
    have : QuasiCompact c := inferInstance
    exact (quasiCompact_iff_compactSpace c).mp this
  have : IsNoetherian C := by constructor
  have : NoetherianSpace C := inferInstance
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  have hd := dim_le_one hD c hS
  refine ⟨fun hfin => hP Ω c hc ?_, fun Z hZ hinf => ?_⟩
  · have hcp : closedPoints C = univ := by
      have : IsClosed (closedPoints C) := by
        have : closedPoints C = ⋃ x ∈ (hfin.subset (subset_univ (closedPoints C))).toFinset, {x} := by
          ext; simp
        rw [this]; exact isClosed_biUnion_finset fun x hx => by simpa using hx
      rw [← this.closure_eq]; exact closure_closedPoints
    have hη : IsClosed ({genericPoint C} : Set C) := by
      rw [← mem_closedPoints_iff, hcp]; trivial
    have : ({genericPoint C} : Set C) = univ := by
      rw [← hη.closure_eq]; exact (genericPoint_spec C).def
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({genericPoint C} : Set C) := this ▸ mem_univ a
    have hb : b ∈ ({genericPoint C} : Set C) := this ▸ mem_univ b
    exact ha.trans hb.symm
  · by_contra hne
    exact hinf (finite_of_closed hd Z hZ hne)

/- English proof (translation)
Introduce `Ω _ _ C c hc hsub`. Take `⟨hI, hPr, hS⟩` from `id hc`. Take `⟨x⟩ : Nonempty C` from `inferInstance`. Establish `: IsAffine C` using `inferInstance`. Set `_ : Field Γ(C, ⊤)` to `(isField_of_isIntegral_of_subsingleton C).toField`.

Establish `hft : (c.appTop).hom.FiniteType` using `(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance`. Set `ι` to `(Scheme.ΓSpecIso (CommRingCat.of Ω))`. Set `φ : Ω →+* Γ(C, ⊤)` to `(c.appTop).hom.comp ι.inv.hom`. Establish `hφ : φ.FiniteType` using `hft.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso ι.inv).2)`. Set `_ : Algebra Ω Γ(C, ⊤)` to `φ.toAlgebra`.

Establish `: Algebra.FiniteType Ω Γ(C, ⊤)` using `hφ`. Establish `: Module.Finite Ω Γ(C, ⊤)` using `finite_of_finite_type_of_isJacobsonRing Ω Γ(C, ⊤)`. Establish `hb : Function.Bijective φ` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Establish `hb2 : Function.Bijective (c.appTop).hom`. Establish `: (c.appTop).hom = φ.comp ι.hom.hom`.

Use extensionality with `a`. Simplify using `[φ]`. Rewrite using `[this]`. Conclude with `hb.comp (ConcreteCategory.bijective_of_isIso ι.hom)`. Establish `: IsIso c.appTop` using `(ConcreteCategory.isIso_iff_bijective _).mpr hb2`.

Establish `: IsIso c`. Establish `h` using `Scheme.isoSpec_hom_naturality c`. Establish `: c = C.isoSpec.hom ≫ Spec.map c.appTop ≫ (Sp Ω).isoSpec.inv`. Rewrite using `[reassoc_of% h]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Use `infer_instance`. Establish `h0 : SmoothOfRelativeDimension 0 c` using `inferInstance`. Conclude with `absurd (ReciprocityTheory.ChartRestriction.G.H1.dim_unique c hS h0 x) (by norm_num)`.
-/
theorem curveNotPoint : LeafCurveNotPoint := by
  intro Ω _ _ C c hc hsub
  obtain ⟨hI, hPr, hS⟩ := id hc
  obtain ⟨x⟩ : Nonempty C := inferInstance
  have : IsAffine C := inferInstance
  let _ : Field Γ(C, ⊤) := (isField_of_isIntegral_of_subsingleton C).toField
  have hft : (c.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω))
  let φ : Ω →+* Γ(C, ⊤) := (c.appTop).hom.comp ι.inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso ι.inv).2)
  let _ : Algebra Ω Γ(C, ⊤) := φ.toAlgebra
  have : Algebra.FiniteType Ω Γ(C, ⊤) := hφ
  have : Module.Finite Ω Γ(C, ⊤) := finite_of_finite_type_of_isJacobsonRing Ω Γ(C, ⊤)
  have hb : Function.Bijective φ := IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hb2 : Function.Bijective (c.appTop).hom := by
    have : (c.appTop).hom = φ.comp ι.hom.hom := by
      ext a; simp [φ]
    rw [this]; exact hb.comp (ConcreteCategory.bijective_of_isIso ι.hom)
  have : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hb2
  have : IsIso c := by
    have h := Scheme.isoSpec_hom_naturality c
    have : c = C.isoSpec.hom ≫ Spec.map c.appTop ≫ (Sp Ω).isoSpec.inv := by
      rw [reassoc_of% h]; simp
    rw [this]; infer_instance
  have h0 : SmoothOfRelativeDimension 0 c := inferInstance
  exact absurd (ReciprocityTheory.ChartRestriction.G.H1.dim_unique c hS h0 x) (by norm_num)

/- English proof (translation)
The claim follows from `LeafCurveSmall_of_cut hD curveNotPoint`.
-/
theorem LeafCurveSmall_of (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall :=
  LeafCurveSmall_of_cut hD curveNotPoint

end LateralTheory.E.CurveKrullDim
