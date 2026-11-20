import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraic
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantSurjective

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

universe u

section Points

variable {F : Type u} [Field F] (C : VariableChange F) {E E' : WeierstrassCurve F}

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `map_variableChange _ _ _`.
-/
theorem baseChange_smul_eq (L : Type*) [Field L] [Algebra F L] (h : C • E = E') :
    C.baseChange L • E.baseChange L = E'.baseChange L := by
  subst h
  exact map_variableChange _ _ _

/- English proof (translation)
Break down `P with _ | ⟨x, y, hP⟩` into its components or cases. Both sides reduce to the same expression. Rewrite using `[vcPoint_some, Point.map_some, Point.map_some, vcPoint_some, Point.some.injEq]`. Establish `hC : (C.baseChange L).map (f : L →+* L') = C.baseChange L'` using `VariableChange.map_baseChange C f`. Prove the components needed by the constructor for the conclusion.

Use `map_vcX (C.baseChange L) (f : L →+* L') x` as an intermediate fact. Rewrite `this` using `[hC]`. Conclude with `this`. Use `map_vcY (C.baseChange L) (f : L →+* L') x y` as an intermediate fact. Rewrite `this` using `[hC]`.

Conclude with `this`.
-/
theorem map_vcPoint {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L'] [DecidableEq L]
    [DecidableEq L'] (f : L →ₐ[F] L') (h : C • E = E') (P : (E.baseChange L).toAffine.Point) :
    Point.map f (vcPoint (C.baseChange L) (baseChange_smul_eq C L h) P) =
      vcPoint (C.baseChange L') (baseChange_smul_eq C L' h) (Point.map f P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, Point.map_some, Point.map_some, vcPoint_some, Point.some.injEq]
    have hC : (C.baseChange L).map (f : L →+* L') = C.baseChange L' :=
      VariableChange.map_baseChange C f
    constructor
    · have := map_vcX (C.baseChange L) (f : L →+* L') x
      rw [hC] at this
      exact this
    · have := map_vcY (C.baseChange L) (f : L →+* L') x y
      rw [hC] at this
      exact this

/- English proof (translation)
Substitute `hD` using the available equality. Break down `P with _ | ⟨x, y, hP⟩` into its components or cases. Both sides reduce to the same expression. Rewrite using `[vcPoint_some, vcPoint_some, Point.some.injEq]`. Establish `hu` using `D.u.inv_mul`.

Simplify using `only [vcX, vcY, VariableChange.inv_def, inv_inv]`. Prove the components needed by the constructor for the conclusion. Take the linear combination `x * (((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu`. Take the linear combination `y * ((((D.u⁻¹ : Lˣ) : L) * D.u) ^ 2 + ((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu`.
-/
theorem vcPoint_vcPoint_of_eq_inv {L : Type*} [Field L] {W W₂ : WeierstrassCurve L}
    (D D' : VariableChange L) (hD : D' = D⁻¹) (h₁ : D • W = W₂) (h₂ : D' • W₂ = W)
    (P : W.toAffine.Point) : vcPoint D' h₂ (vcPoint D h₁ P) = P := by
  subst hD
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, vcPoint_some, Point.some.injEq]
    have hu := D.u.inv_mul
    simp only [vcX, vcY, VariableChange.inv_def, inv_inv]
    constructor
    · linear_combination x * (((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu
    · linear_combination y * ((((D.u⁻¹ : Lˣ) : L) * D.u) ^ 2 + ((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Conclude with `vcPoint_injective D h (e.trans (vcPoint_zero D h).symm)`. Introduce and unpack `rfl`. Both sides reduce to the same expression.
-/
theorem vcPoint_eq_zero_iff {L : Type*} [Field L] {W W₂ : WeierstrassCurve L} (D : VariableChange L)
    (h : D • W = W₂) {P : W.toAffine.Point} : vcPoint D h P = 0 ↔ P = 0 := by
  constructor
  · intro e
    exact vcPoint_injective D h (e.trans (vcPoint_zero D h).symm)
  · rintro rfl
    rfl

end Points

section Hom

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (C : VariableChange F)
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

def vcPt (h : C • E = E') : (E'.baseChange E.toAffine.FunctionField).toAffine.Point :=
  vcPoint (C.baseChange _) (baseChange_smul_eq C _ h) (genericPoint E)

/- English proof (translation)
Introduce `L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hs`. Simplify using `only [ratMapValue, vcPt]`. Rewrite using `[map_vcPoint C _ h, map_vcPoint C _ h, map_vcPoint C _ h, map_liftPoint_genericPoint E h₁ t₁, map_liftPoint_genericPoint E h₂ t₂, map_liftPoint_genericPoint E h₃ t₃, ← vcPoint_add, hs]`.
-/
theorem respectsAdd_vcPt (h : C • E = E') : RespectsAdd E E' (vcPt C h) := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hs
  simp only [ratMapValue, vcPt]
  rw [map_vcPoint C _ h, map_vcPoint C _ h, map_vcPoint C _ h, map_liftPoint_genericPoint E h₁ t₁,
    map_liftPoint_genericPoint E h₂ t₂, map_liftPoint_genericPoint E h₃ t₃, ← vcPoint_add, hs]

def vcHom (h : C • E = E') : isogHom E E' := ⟨vcPt C h, respectsAdd_vcPt C h⟩

/- English proof (translation)
Rewrite using `[vcPt, Ne, vcPoint_eq_zero_iff]`. Conclude with `isGenPt_ne_zero E isGenPt_genericPoint`.
-/
theorem vcPt_ne_zero (h : C • E = E') : vcPt C h ≠ 0 := by
  rw [vcPt, Ne, vcPoint_eq_zero_iff]
  exact isGenPt_ne_zero E isGenPt_genericPoint

/- English proof (translation)
The claim follows from `isGenPt_of_mem_isogHom (vcHom C h).2 (vcPt_ne_zero C h)`.
-/
theorem isGenPt_vcHom (h : C • E = E') : IsGenPt E' (vcHom C h).1 :=
  isGenPt_of_mem_isogHom (vcHom C h).2 (vcPt_ne_zero C h)

/- English proof (translation)
The claim follows from `map_vcPoint C g h (genericPoint E)`.
-/
theorem map_vcHom {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (g : E.toAffine.FunctionField →ₐ[F] L) (h : C • E = E') :
    Point.map g (vcHom C h).1 =
      vcPoint (C.baseChange L) (baseChange_smul_eq C L h) (Point.map g (genericPoint E)) :=
  map_vcPoint C g h (genericPoint E)

omit [IsAlgClosed F] [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in
/- English proof (translation)
Rewrite using `[← h, inv_smul_smul]`.
-/
theorem inv_smul_eq_of_smul_eq (h : C • E = E') : C⁻¹ • E' = E := by
  rw [← h, inv_smul_smul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[homComp_of_isGenPt _ _ (isGenPt_vcHom C h)]`. Rewrite using `[map_vcHom, map_genEval_genericPoint]`. Establish `hD' : D.baseChange E.toAffine.FunctionField = (C.baseChange E.toAffine.FunctionField)⁻¹`. Substitute `hD` using the available equality.

Conclude with `map_inv (VariableChange.mapHom (algebraMap F E.toAffine.FunctionField)) C`. Conclude with `vcPoint_vcPoint_of_eq_inv _ _ hD' (baseChange_smul_eq C _ h) (baseChange_smul_eq D _ h') (genericPoint E)`.
-/
theorem homComp_vcHom_vcHom (D : VariableChange F) (hD : D = C⁻¹) (h : C • E = E')
    (h' : D • E' = E) : homComp (vcHom D h') (vcHom C h) = homId := by
  apply Subtype.ext
  rw [homComp_of_isGenPt _ _ (isGenPt_vcHom C h)]
  rw [map_vcHom, map_genEval_genericPoint]
  have hD' : D.baseChange E.toAffine.FunctionField = (C.baseChange E.toAffine.FunctionField)⁻¹ := by
    subst hD
    exact map_inv (VariableChange.mapHom (algebraMap F E.toAffine.FunctionField)) C
  exact vcPoint_vcPoint_of_eq_inv _ _ hD' (baseChange_smul_eq C _ h) (baseChange_smul_eq D _ h')
    (genericPoint E)

def vcEndEquiv (h : C • E = E') : isogEnd E ≃+* isogEnd E' where
  toFun f := homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)))
  invFun g := homComp (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) (homComp g (vcHom C h))
  left_inv f := by
    simp only [homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_right]
    rw [← homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_left]
  right_inv g := by
    simp only [homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_right]
    rw [← homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_left]
  map_mul' f g := by
    simp only [isogEnd_mul_def, homComp_assoc]
    rw [← homComp_assoc (vcHom C⁻¹ _) (vcHom C h),
      homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homComp_id_left]
  map_add' f g := by
    rw [homComp_add_left, homComp_add_right]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vcEndEquiv_apply (h : C • E = E') (f : isogEnd E) :
    vcEndEquiv C h f = homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))) :=
  rfl

end Hom

section Const

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

/- English proof (translation)
Distinguish the cases in `hQ : IsGenPt E' Q.1`. Use `set g := genEval E' Q.1 hQ`. Establish `key : algebraMap F E.toAffine.FunctionField (homConst E' E'' R * homConst E E' Q) • invariantDifferential E = omegaAt E'' (homComp R Q).1`. Rewrite using `[homComp_of_isGenPt _ _ hQ, ← kpush_omegaAt, omegaAt_eq_homConst_smul, ← algebraMap_smul E'.toAffine.FunctionField (homConst E' E'' R) (invariantDifferential E'), kpush_smul, AlgHom.commutes, show invariantDifferential E' = omegaAt E' (genericPoint E') from rfl, kpush_omegaAt, ma …`. Apply `(algebraMap F E.toAffine.FunctionField).injective` to reduce the goal to its premises.

Rewrite using `[algebraMap_homConst]`. Establish `h2` using `homCoeff_smul (homComp R Q)`. Rewrite `h2` using `[← key]`. Conclude with `smul_left_injective _ (invariantDifferential_ne_zero E) h2`. Rewrite using `[eq_zero_of_not_isGenPt Q hQ, homComp_zero_right, map_zero, map_zero, mul_zero]`.
-/
theorem homConst_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homConst E E'' (homComp R Q) = homConst E' E'' R * homConst E E' Q := by
  by_cases hQ : IsGenPt E' Q.1
  · set g := genEval E' Q.1 hQ
    have key : algebraMap F E.toAffine.FunctionField (homConst E' E'' R * homConst E E' Q) •
        invariantDifferential E = omegaAt E'' (homComp R Q).1 := by
      rw [homComp_of_isGenPt _ _ hQ, ← kpush_omegaAt, omegaAt_eq_homConst_smul,
        ← algebraMap_smul E'.toAffine.FunctionField (homConst E' E'' R) (invariantDifferential E'),
        kpush_smul, AlgHom.commutes,
        show invariantDifferential E' = omegaAt E' (genericPoint E') from rfl, kpush_omegaAt, map_genEval_genericPoint,
        omegaAt_eq_homConst_smul, ← algebraMap_smul E.toAffine.FunctionField (homConst E E' Q),
        smul_smul, ← map_mul]
    apply (algebraMap F E.toAffine.FunctionField).injective
    rw [algebraMap_homConst]
    have h2 := homCoeff_smul (homComp R Q)
    rw [← key] at h2
    exact smul_left_injective _ (invariantDifferential_ne_zero E) h2
  · rw [eq_zero_of_not_isGenPt Q hQ, homComp_zero_right, map_zero, map_zero, mul_zero]

/- English proof (translation)
Apply `(algebraMap F E.toAffine.FunctionField).injective` to reduce the goal to its premises. Rewrite using `[algebraMap_homConst, map_one]`. Conclude with `invCoeff_invariantDifferential E`.
-/
theorem homConst_homId : homConst E E (homId : isogEnd E) = 1 := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, map_one]
  exact invCoeff_invariantDifferential E

variable (E) in

def endConst : isogEnd E →+* F where
  toFun := homConst E E
  map_one' := homConst_homId
  map_mul' f g := homConst_homComp f g
  map_zero' := map_zero _
  map_add' := map_add _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem endConst_apply (f : isogEnd E) : endConst E f = homConst E E f := rfl

/- English proof (translation)
Establish `e` using `homConst_homComp (vcHom C h) (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))`. Rewrite `e` using `[homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homConst_homId]`. Rewrite using `[endConst_apply, endConst_apply, vcEndEquiv_apply, homConst_homComp, homConst_homComp]`. Take the linear combination `(-(homConst E E f)) * e`.
-/
theorem endConst_vcEndEquiv (C : VariableChange F) (h : C • E = E') (f : isogEnd E) :
    endConst E' (vcEndEquiv C h f) = endConst E f := by
  have e := homConst_homComp (vcHom C h) (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))
  rw [homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h,
    homConst_homId] at e
  rw [endConst_apply, endConst_apply, vcEndEquiv_apply, homConst_homComp, homConst_homComp]
  linear_combination (-(homConst E E f)) * e

end Const

section Complex

variable {E : WeierstrassCurve ℂ} [E.IsElliptic]

/- English proof (translation)
The claim follows from `homConst_latticeEndEquiv L α`.
-/
theorem endConst_latticeEndEquiv (L : PeriodPair) (α : latticeEnd L) :
    endConst (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeEndEquiv L α

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, rfl⟩`. Take `⟨α, rfl⟩` from `(latticeEndEquiv L).surjective f`. Rewrite using `[endConst_latticeEndEquiv]`.

Conclude with `α.2`. Introduce `hz`. Conclude with `⟨latticeEndEquiv L ⟨z, hz⟩, endConst_latticeEndEquiv L ⟨z, hz⟩⟩`.
-/
theorem range_endConst_weierstrassCurve (L : PeriodPair) :
    (endConst (weierstrassCurve L)).range = latticeEnd L := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨α, rfl⟩ := (latticeEndEquiv L).surjective f
    rw [endConst_latticeEndEquiv]
    exact α.2
  · intro hz
    exact ⟨latticeEndEquiv L ⟨z, hz⟩, endConst_latticeEndEquiv L ⟨z, hz⟩⟩

/- English proof (translation)
Take `⟨L, C, hC⟩` from `exists_variableChange_eq_weierstrassCurve E`. Introduce `f g hfg`. Apply `(vcEndEquiv C hC).injective` to reduce the goal to its premises. Apply `(latticeEndEquiv L).symm.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hf` using `endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC f))`. Establish `hg` using `endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC g))`. Rewrite `hf`, `hg` using `[RingEquiv.apply_symm_apply, endConst_vcEndEquiv]`. Rewrite using `[← hf, ← hg, hfg]`.
-/
theorem endConst_injective : Function.Injective (endConst E) := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve E
  intro f g hfg
  apply (vcEndEquiv C hC).injective
  apply (latticeEndEquiv L).symm.injective
  apply Subtype.ext
  have hf := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC f))
  have hg := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC g))
  rw [RingEquiv.apply_symm_apply, endConst_vcEndEquiv] at hf hg
  rw [← hf, ← hg, hfg]

/- English proof (translation)
Rewrite using `[← range_endConst_weierstrassCurve]`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, rfl⟩`. Conclude with `⟨vcEndEquiv C hC f, endConst_vcEndEquiv C hC f⟩`.

Introduce and unpack `⟨g, rfl⟩`. Take `⟨f, rfl⟩` from `(vcEndEquiv C hC).surjective g`. Conclude with `⟨f, (endConst_vcEndEquiv C hC f).symm⟩`.
-/
theorem range_endConst {L : PeriodPair} {C : VariableChange ℂ} (hC : C • E = weierstrassCurve L) :
    (endConst E).range = latticeEnd L := by
  rw [← range_endConst_weierstrassCurve]
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨vcEndEquiv C hC f, endConst_vcEndEquiv C hC f⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨f, rfl⟩ := (vcEndEquiv C hC).surjective g
    exact ⟨f, (endConst_vcEndEquiv C hC f).symm⟩

end Complex

end Elliptic
end GroundTheory.Global
