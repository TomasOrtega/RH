import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_fixGrp, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `h _ ⟨x, rfl⟩`.

Introduce and unpack `h _ ⟨x, rfl⟩`. Conclude with `h x`.
-/
private theorem fixingSubgroup_fieldRange {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (K : Type) [Field K]
    [Algebra E K] [Algebra K Ω] [IsScalarTower E K Ω] :
    (IsScalarTower.toAlgHom E K Ω).fieldRange.fixingSubgroup = fixGrp E Ω K := by
  ext g
  rw [mem_fixGrp, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ X Y hXY`. Establish `hGal : IsGalois E Ω` using `inferInstance`. Use `set f := IsScalarTower.toAlgHom E X.K Ω`. Use `set g := IsScalarTower.toAlgHom E Y.K Ω`. Establish `hX` using `fixingSubgroup_fieldRange (E := E) (Ω := Ω) X.K`.

Establish `hY` using `fixingSubgroup_fieldRange (E := E) (Ω := Ω) Y.K`. Establish `hle : f.fieldRange ≤ g.fieldRange`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup f.fieldRange, ← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange]`. Apply `IntermediateField.fixedField_le` to reduce the goal to its premises. Rewrite using `[hX, hY]`.

Conclude with `hXY`. Use `set eX := AlgEquiv.ofInjectiveField f`. Use `set eY := AlgEquiv.ofInjectiveField g`. Use `set φ : X.K →ₐ[E] Y.K := (eY.symm.toAlgHom.comp (IntermediateField.inclusion hle)).comp eX.toAlgHom`. Establish `hφ : ∀ x : X.K, g (φ x) = f x`.

Introduce `x`. Establish `h1 : (eY (φ x) : Ω) = g (φ x)` using `rfl`. Rewrite using `[← h1]`. Establish `h2 : eY (φ x) = IntermediateField.inclusion hle (eX x)` using `eY.apply_symm_apply _`. Rewrite using `[h2]`.

Both sides reduce to the same expression. Use `letI alg : Algebra X.K Y.K := φ.toRingHom.toAlgebra`. Establish `t1 : IsScalarTower E X.K Y.K` using `IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)`. Establish `t2 : IsScalarTower X.K Y.K Ω` using `IsScalarTower.of_algebraMap_eq (fun x => (hφ x).symm)`. Use `⟨alg, t1, t2, IsGalois.tower_top_of_isGalois E X.K Y.K, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hX, ← hY]`. Establish `iX` using `IntermediateField.finrank_eq_fixingSubgroup_index Ω f.fieldRange`. Establish `iY` using `IntermediateField.finrank_eq_fixingSubgroup_index Ω g.fieldRange`. Establish `fX : Module.finrank E X.K = Module.finrank E f.fieldRange` using `eX.toLinearEquiv.finrank_eq`. Establish `fY : Module.finrank E Y.K = Module.finrank E g.fieldRange` using `eY.toLinearEquiv.finrank_eq`.

Establish `tw` using `Module.finrank_mul_finrank E X.K Y.K`. Establish `hsub : g.fieldRange.fixingSubgroup ≤ f.fieldRange.fixingSubgroup`. Rewrite using `[hX, hY]`. Conclude with `hXY`. Establish `rel` using `Subgroup.relIndex_mul_index hsub`.

Use `haveI : FiniteDimensional E X.K := Module.Finite.of_restrictScalars_finite ℚ E X.K`. Establish `hpos : 0 < Module.finrank E X.K` using `Module.finrank_pos`. Rewrite `tw`, `hpos` using `[fX, iX]`. Rewrite `tw` using `[fY, iY, ← rel]`. Conclude with `Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm] at tw; exact tw)`.
-/
theorem inclOf : InclOf := by
  intro E Ω _ _ _ _ _ _ X Y hXY
  have hGal : IsGalois E Ω := inferInstance
  set f := IsScalarTower.toAlgHom E X.K Ω
  set g := IsScalarTower.toAlgHom E Y.K Ω
  have hX := fixingSubgroup_fieldRange (E := E) (Ω := Ω) X.K
  have hY := fixingSubgroup_fieldRange (E := E) (Ω := Ω) Y.K
  have hle : f.fieldRange ≤ g.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup f.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange]
    apply IntermediateField.fixedField_le
    rw [hX, hY]
    exact hXY
  set eX := AlgEquiv.ofInjectiveField f
  set eY := AlgEquiv.ofInjectiveField g
  set φ : X.K →ₐ[E] Y.K := (eY.symm.toAlgHom.comp (IntermediateField.inclusion hle)).comp eX.toAlgHom
  have hφ : ∀ x : X.K, g (φ x) = f x := by
    intro x
    have h1 : (eY (φ x) : Ω) = g (φ x) := rfl
    rw [← h1]
    have h2 : eY (φ x) = IntermediateField.inclusion hle (eX x) := eY.apply_symm_apply _
    rw [h2]
    rfl
  letI alg : Algebra X.K Y.K := φ.toRingHom.toAlgebra
  have t1 : IsScalarTower E X.K Y.K := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  have t2 : IsScalarTower X.K Y.K Ω := IsScalarTower.of_algebraMap_eq (fun x => (hφ x).symm)
  refine ⟨alg, t1, t2, IsGalois.tower_top_of_isGalois E X.K Y.K, ?_⟩
  rw [← hX, ← hY]
  have iX := IntermediateField.finrank_eq_fixingSubgroup_index Ω f.fieldRange
  have iY := IntermediateField.finrank_eq_fixingSubgroup_index Ω g.fieldRange
  have fX : Module.finrank E X.K = Module.finrank E f.fieldRange := eX.toLinearEquiv.finrank_eq
  have fY : Module.finrank E Y.K = Module.finrank E g.fieldRange := eY.toLinearEquiv.finrank_eq
  have tw := Module.finrank_mul_finrank E X.K Y.K
  have hsub : g.fieldRange.fixingSubgroup ≤ f.fieldRange.fixingSubgroup := by
    rw [hX, hY]; exact hXY
  have rel := Subgroup.relIndex_mul_index hsub
  haveI : FiniteDimensional E X.K := Module.Finite.of_restrictScalars_finite ℚ E X.K
  have hpos : 0 < Module.finrank E X.K := Module.finrank_pos
  rw [fX, iX] at tw hpos
  rw [fY, iY, ← rel] at tw
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm] at tw; exact tw)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
