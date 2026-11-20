import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TPullTMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH UpperTheory.Ru.crystallineComparison UpperTheory.Ru.crystallineComparison.Th

noncomputable section

namespace UpperTheory.Ru.crystallineComparison.Th.Deg0

open ComposableArrows GlobalTheory.CatH

section Gen

variable {R : Type} [CommRing R] {E : Type 1} [Category.{0} E] {G : E ⥤ ModuleCat.{1} R}

private def val (f : Cn G 0) (X : E) : G.obj X := f (mk₀ X)

private def dv (f : Cn G 0) {X Y : E} (φ : X ⟶ Y) : G.obj Y := d G 0 f (mk₁ φ)

/- English proof (translation)
The claim follows from `eq_of_heq (congr_arg_heq f (ext₀ rfl))`.
-/
private theorem val_eq (f : Cn G 0) (s : ComposableArrows E 0) : f s = val f (s.obj (Fin.last 0)) :=
  eq_of_heq (congr_arg_heq f (ext₀ rfl))

/- English proof (translation)
Establish `e0 : (f (face 0 (mk₁ φ))) = val f Y` using `val_eq f _`. Establish `e1 : (f (face 1 (mk₁ φ))) = val f X` using `val_eq f _`. Establish `t0 : (toLast 0 (mk₁ φ) : Y ⟶ Y) = 𝟙 Y` using `(mk₁ φ).map_id _`. Establish `t1 : (toLast 1 (mk₁ φ) : X ⟶ Y) = φ` using `rfl`. Establish `h : dv f φ = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (G.map (toLast i (mk₁ φ))).hom (f (face i (mk₁ φ)))` using `rfl`.

Rewrite using `[h, Fin.sum_univ_two]`. Establish `a0 : (G.map (toLast 0 (mk₁ φ))).hom (f (face 0 (mk₁ φ))) = val f Y`. Establish `: ∀ m : Y ⟶ Y, m = 𝟙 Y → (G.map m).hom (val f Y) = val f Y`. Introduce and unpack `m rfl`. Simplify using the standard rewrite rules.

Conclude with `(congrArg (G.map (toLast 0 (mk₁ φ))).hom e0).trans (this _ t0)`. Establish `a1 : (G.map (toLast 1 (mk₁ φ))).hom (f (face 1 (mk₁ φ))) = (G.map φ).hom (val f X)` using `congrArg (G.map φ).hom e1`. Rewrite using `[a0, a1]`. Simplify using `[sub_eq_add_neg]`.
-/
private theorem dv_eq (f : Cn G 0) {X Y : E} (φ : X ⟶ Y) :
    dv f φ = val f Y - (G.map φ).hom (val f X) := by
  have e0 : (f (face 0 (mk₁ φ))) = val f Y := val_eq f _
  have e1 : (f (face 1 (mk₁ φ))) = val f X := val_eq f _
  have t0 : (toLast 0 (mk₁ φ) : Y ⟶ Y) = 𝟙 Y := (mk₁ φ).map_id _
  have t1 : (toLast 1 (mk₁ φ) : X ⟶ Y) = φ := rfl
  have h : dv f φ = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (G.map (toLast i (mk₁ φ))).hom (f (face i (mk₁ φ))) := rfl
  rw [h, Fin.sum_univ_two]
  have a0 : (G.map (toLast 0 (mk₁ φ))).hom (f (face 0 (mk₁ φ))) = val f Y := by
    have : ∀ m : Y ⟶ Y, m = 𝟙 Y → (G.map m).hom (val f Y) = val f Y := by
      rintro m rfl; simp
    exact (congrArg (G.map (toLast 0 (mk₁ φ))).hom e0).trans (this _ t0)
  have a1 : (G.map (toLast 1 (mk₁ φ))).hom (f (face 1 (mk₁ φ))) = (G.map φ).hom (val f X) :=
    congrArg (G.map φ).hom e1
  rw [a0, a1]
  simp [sub_eq_add_neg]

end Gen

variable {C : Type 1} [Category.{0} C]

private def ofZ (P : C ⥤ Type) (F : Coef C) (f : (cx (elF P (zm F))).Z 0) : Sec P F :=
  ⟨fun A y => val f.1 (P.elementsMk A y), by
    intro A B φ y
    have h : dv f.1 (⟨φ, rfl⟩ : P.elementsMk A y ⟶ P.elementsMk B (P.map φ y)) = 0 :=
      congrFun (LinearMap.mem_ker.1 f.2) _
    rw [dv_eq] at h
    exact (sub_eq_zero.1 h).symm⟩

private def toZ (P : C ⥤ Type) (F : Coef C) (c : Sec P F) : (cx (elF P (zm F))).Z 0 :=
  ⟨fun s => c.1 _ (s.obj (Fin.last 0)).2, by
    refine LinearMap.mem_ker.2 (funext fun s => ?_)
    obtain ⟨X, Y, φ, rfl⟩ := mk₁_surjective s
    refine (dv_eq (G := elF P (zm F)) _ φ).trans (sub_eq_zero.2 ?_)
    have h := c.2 φ.1 X.2
    rw [φ.2] at h
    exact h.symm⟩

private def zEq (P : C ⥤ Type) (F : Coef C) : (cx (elF P (zm F))).Z 0 ≃+ Sec P F where
  toFun := ofZ P F
  invFun := toZ P F
  left_inv f := Subtype.ext (funext fun s => (val_eq f.1 s).symm)
  right_inv c := Subtype.ext rfl
  map_add' _ _ := rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_bot]`. Conclude with `⟨fun h => Subtype.ext h, fun h => by rw [h]; exact Submodule.zero_mem _⟩`.
-/
private theorem bot_of {R : Type} [CommRing R] (K : Cx.{1} R) : (K.B 0).submoduleOf (K.Z 0) = ⊥ := by
  ext x
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_bot]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; exact Submodule.zero_mem _⟩

private def zIso (P : C ⥤ Type) (F : Coef C) : TH P F 0 ≃+ Sec P F :=
  (Submodule.quotEquivOfEqBot _ (bot_of (cx (elF P (zm F))))).toAddEquiv.trans (zEq P F)

end UpperTheory.Ru.crystallineComparison.Th.Deg0

open UpperTheory.Ru.crystallineComparison.Th.Deg0 in
/- English proof (translation)
Introduce `C _`. Use `⟨zIso, ?_, ?_⟩` and prove the remaining obligations. Introduce `Q P u F x A y`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `val_eq f.1 _`.

Introduce `P F G α x A y`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `congrArg (α.app A).hom (val_eq f.1 _)`.
-/
theorem UpperTheory.exists_cohomology_zero_equiv_sections_natural :
    ∀ (C : Type 1) [Category.{0} C], ∃ z : ∀ (P : C ⥤ Type) (F : Coef C), TH P F 0 ≃+ Sec P F,
        (∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (F : Coef C) (x : TH P F 0) (A : C) (y : Q.obj A),
          (z Q F (tPull u F 0 x)).1 A y = (z P F x).1 A (u.app A y)) ∧
        ∀ (P : C ⥤ Type) {F G : Coef C} (α : F ⟶ G) (x : TH P F 0) (A : C) (y : P.obj A),
          (z P G (tMap P α 0 x)).1 A y = (α.app A).hom ((z P F x).1 A y) := by
  intro C _
  refine ⟨zIso, ?_, ?_⟩
  · intro Q P u F x A y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact val_eq f.1 _
  · intro P F G α x A y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg (α.app A).hom (val_eq f.1 _)
