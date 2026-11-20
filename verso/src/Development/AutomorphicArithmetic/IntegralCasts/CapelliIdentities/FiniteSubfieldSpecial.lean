import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp R' ⟶ UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

/- English proof (translation)
Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra ℤ A).FG)`. Use `⟨IntermediateField.adjoin ℚ (φ '' (s : Set A)), ?_, ?_⟩` and prove the remaining obligations. Establish `: Finite (φ '' (s : Set A))` using `(s.finite_toSet.image φ).to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)`. Introduce `a`.

Establish `ha : a ∈ Algebra.adjoin ℤ (s : Set A)` using `by rw [hs]; trivial`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩`. Consider the case `algebraMap r`. Establish `: φ (algebraMap ℤ A r) = (r : C)` using `by simp`.

Rewrite using `[this]`. Conclude with `intCast_mem _ r`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `mul_mem hx hy`.
-/
private lemma UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield {A C : Type} [CommRing A] [Field C] [CharZero C]
    [Algebra.IsAlgebraic ℚ C] [Algebra.FiniteType ℤ A] (φ : A →+* C) :
    ∃ K : IntermediateField ℚ C, FiniteDimensional ℚ K ∧ ∀ a, φ a ∈ K := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ A).FG)
  refine ⟨IntermediateField.adjoin ℚ (φ '' (s : Set A)), ?_, ?_⟩
  · have : Finite (φ '' (s : Set A)) := (s.finite_toSet.image φ).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  · intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap ℤ A r) = (r : C) := by simp
      rw [this]
      exact intCast_mem _ r
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

open AlgebraicGeometry CategoryTheory in
/- English proof (translation)
Introduce `C _ _ _ X π _ x`. Set `pt : Spec (CommRingCat.of C)` to `IsLocalRing.closedPoint C`. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x pt) (U := ⊤) trivial`. Establish `hrange : Set.range x ⊆ Set.range hU.fromSpec`. Rewrite using `[hU.range_fromSpec]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Establish `: y = pt` using `Subsingleton.elim _ _`. Rewrite using `[this]`. Conclude with `hxU`. Set `y` to `IsOpenImmersion.lift hU.fromSpec x hrange`.

Establish `hy : y ≫ hU.fromSpec = x` using `IsOpenImmersion.lift_fac _ _ _`. Set `φ : Γ(X, U) →+* C` to `(Spec.preimage y).hom`. Establish `hφ : Spec.map (CommRingCat.ofHom φ) = y` using `Spec.map_preimage y`. Establish `hft : (π.appLE ⊤ U (by simp)).hom.FiniteType` using `π.finiteType_appLE (isAffineOpen_top _) hU _`. Establish `hft' : ((π.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType` using `RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2))`.

Establish `hA : Algebra.FiniteType ℤ Γ(X, U)`. Establish `h : algebraMap ℤ Γ(X, U) = ((π.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)` using `Subsingleton.elim _ _`. Rewrite `hft'` using `[← h]`. Conclude with `RingHom.finiteType_algebraMap.mp hft'`. Take `⟨K, hK, hmem⟩` from `UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield φ`.

Set `ψ : Γ(X, U) →+* K` to `φ.codRestrict K hmem`. Use `⟨K, inferInstance, { to_finiteDimensional := hK }, K.val.toRingHom, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, ← hφ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.main :
    ∀ (C : Type) [inst : Field C] [inst_1 : CharZero C] [Algebra.IsAlgebraic ℚ C] (X : AlgebraicGeometry.Scheme)
      (π : X ⟶ UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp ℤ) [AlgebraicGeometry.LocallyOfFiniteType π] (x : UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp C ⟶ X),
      ∃ (K : Type) (x_1 : Field K) (_ : NumberField K) (e : K →+* C) (x' : UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp K ⟶ X),
        CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.spMap e) x' = x := by
  intro C _ _ _ X π _ x
  let pt : Spec (CommRingCat.of C) := IsLocalRing.closedPoint C
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x pt) (U := ⊤) trivial
  have hrange : Set.range x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y = pt := Subsingleton.elim _ _
    rw [this]
    exact hxU
  let y := IsOpenImmersion.lift hU.fromSpec x hrange
  have hy : y ≫ hU.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, U) →+* C := (Spec.preimage y).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = y := Spec.map_preimage y
  have hft : (π.appLE ⊤ U (by simp)).hom.FiniteType :=
    π.finiteType_appLE (isAffineOpen_top _) hU _
  have hft' : ((π.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2))
  have hA : Algebra.FiniteType ℤ Γ(X, U) := by
    have h : algebraMap ℤ Γ(X, U) = ((π.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom) := Subsingleton.elim _ _
    rw [← h] at hft'
    exact RingHom.finiteType_algebraMap.mp hft'
  obtain ⟨K, hK, hmem⟩ := UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield φ
  let ψ : Γ(X, U) →+* K := φ.codRestrict K hmem
  refine ⟨K, inferInstance, { to_finiteDimensional := hK }, K.val.toRingHom,
    Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  rw [← hy, ← hφ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
