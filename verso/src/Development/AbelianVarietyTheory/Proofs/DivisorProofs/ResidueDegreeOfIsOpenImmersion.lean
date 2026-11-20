import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DegreeAdditiveFrobenius
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CurveDegreesCompare

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in

/- English proof (translation)
Use `letI := (g.residueFieldMap (f x)).hom.toAlgebra`. Use `letI := (f.residueFieldMap x).hom.toAlgebra`. Use `letI : Algebra (Z.residueField (g (f x))) (X.residueField x) := ((f ≫ g).residueFieldMap x).hom.toAlgebra`. Use `haveI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x) := by`. Use `IsScalarTower.of_algebraMap_eq' ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((f ≫ g).residueFieldMap x).hom = _`. Rewrite using `[Scheme.residueFieldMap_comp]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Module.finrank (Z.residueField (g (f x))) (X.residueField x) = Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) * Module.finrank (Y.residueField (f x)) (X.residueField x)`. Conclude with `(Module.finrank_mul_finrank _ _ _).symm`.
-/
theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((f ≫ g).residueFieldMap x).hom = _
    rw [Scheme.residueFieldMap_comp]
    rfl
  change Module.finrank (Z.residueField (g (f x))) (X.residueField x) =
    Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank _ _ _).symm

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in

/- English proof (translation)
Use `letI := (f.residueFieldMap x).hom.toAlgebra`. Establish `hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x))` using `ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)`. Set `e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x` to `(AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv`. Express the relevant statement in the definitionally equal form `Module.finrank (Y.residueField (f x)) (X.residueField x) = 1`. Rewrite using `[← e.finrank_eq, Module.finrank_self]`.
-/
theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : f.residueDegree x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)
  let e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [← e.finrank_eq, Module.finrank_self]

/- English proof (translation)
Substitute `hx` using the available equality. Use `letI := (X.Γevaluation (genericPoint X)).hom.toAlgebra`. Use `haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩`. Use `functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)` as an intermediate fact. Set `φ : X.functionField →+* X.residueField (genericPoint X)` to `(X.residue _).hom`.

Set `e : X.functionField ≃ₐ[Γ(X, ⊤)] X.residueField (genericPoint X)` to `{ RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with commutes' := fun _ => rfl }`. Conclude with `IsLocalization.isLocalization_of_algEquiv _ e`.
-/
theorem isFractionRing_residueField (X : Scheme.{0}) [IsIntegral X] [IsAffine X] {x : X}
    (hx : x = genericPoint X) :
    letI := (X.Γevaluation x).hom.toAlgebra
    IsFractionRing Γ(X, ⊤) (X.residueField x) := by
  subst hx
  letI := (X.Γevaluation (genericPoint X)).hom.toAlgebra
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, ⊤)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

/- English proof (translation)
Rewrite using `[genericPoint_eq_of_isOpenImmersion, genericPoint_eq_bot_of_affine]`. Use `letI := g.appTop.hom.toAlgebra`. Use `letI := (g.residueFieldMap (genericPoint P)).hom.toAlgebra`. Use `letI := (T.Γevaluation (g (genericPoint P))).hom.toAlgebra`. Use `letI := (P.Γevaluation (genericPoint P)).hom.toAlgebra`.

Use `haveI := isFractionRing_residueField T hg`. Use `haveI := isFractionRing_residueField P rfl`. Use `letI : Algebra Γ(T, ⊤) (P.residueField (genericPoint P)) := (g.appTop ≫ P.Γevaluation (genericPoint P)).hom.toAlgebra`. Use `haveI : IsScalarTower Γ(T, ⊤) Γ(P, ⊤) (P.residueField (genericPoint P)) := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower Γ(T, ⊤) (T.residueField (g (genericPoint P))) (P.residueField (genericPoint P)) := IsScalarTower.of_algebraMap_eq' congr($(Scheme.Γevaluation_naturality g _).hom).symm`.

Establish `h : (⊥ : PrimeSpectrum Γ(T, ⊤)).asIdeal.primeCompl ≤ nonZeroDivisors Γ(T, ⊤)` using `fun x hx => mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)`. Use `Eq.trans ?_ (IsFractionRing.finrank_eq Γ(T, ⊤) _ Γ(P, ⊤) _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Module.rankAtStalk (R := Γ(T, ⊤)) Γ(P, ⊤) ⊥ = _`. Rewrite using `[Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]`. Conclude with `IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ _) h`.
-/
theorem finrank_appTop_eq {P T : Scheme.{0}} [IsIntegral P] [IsIntegral T] [IsAffine P]
    [IsAffine T] (g : P ⟶ T) (hg : g (genericPoint P) = genericPoint T) :
    g.appTop.hom.finrank (T.isoSpec.hom (genericPoint T)) = g.residueDegree (genericPoint P) := by
  rw [genericPoint_eq_of_isOpenImmersion, genericPoint_eq_bot_of_affine]
  letI := g.appTop.hom.toAlgebra
  letI := (g.residueFieldMap (genericPoint P)).hom.toAlgebra
  letI := (T.Γevaluation (g (genericPoint P))).hom.toAlgebra
  letI := (P.Γevaluation (genericPoint P)).hom.toAlgebra
  haveI := isFractionRing_residueField T hg
  haveI := isFractionRing_residueField P rfl
  letI : Algebra Γ(T, ⊤) (P.residueField (genericPoint P)) :=
    (g.appTop ≫ P.Γevaluation (genericPoint P)).hom.toAlgebra
  haveI : IsScalarTower Γ(T, ⊤) Γ(P, ⊤) (P.residueField (genericPoint P)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(T, ⊤) (T.residueField (g (genericPoint P)))
      (P.residueField (genericPoint P)) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.Γevaluation_naturality g _).hom).symm
  have h : (⊥ : PrimeSpectrum Γ(T, ⊤)).asIdeal.primeCompl ≤ nonZeroDivisors Γ(T, ⊤) := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)
  refine Eq.trans ?_ (IsFractionRing.finrank_eq Γ(T, ⊤) _ Γ(P, ⊤) _).symm
  change Module.rankAtStalk (R := Γ(T, ⊤)) Γ(P, ⊤) ⊥ = _
  rw [Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]
  exact IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ _) h

/- English proof (translation)
Set `ι` to `C.affineOpenCover.f (C.affineOpenCover.idx (genericPoint C))`. Set `t` to `(C.affineOpenCover.covers (genericPoint C)).choose`. Establish `ht : ι t = genericPoint C` using `(C.affineOpenCover.covers (genericPoint C)).choose_spec`. Take `⟨y, hy, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := π) (g := ι) _ t (h.trans ht.symm)`. Use `haveI : Nonempty _ := ⟨t⟩`.

Use `haveI := isIntegral_of_isOpenImmersion ι`. Use `haveI : Nonempty ↥(pullback π ι) := ⟨y⟩`. Use `haveI := isIntegral_of_isOpenImmersion (pullback.fst π ι)`. Use `haveI : IsAffine (pullback π ι) := isAffine_of_isAffineHom (pullback.snd π ι)`. Establish `e₀` using `genericPoint_eq_of_isOpenImmersion ι`.

Establish `e₁` using `genericPoint_eq_of_isOpenImmersion (pullback.fst π ι)`. Establish `e₂ : pullback.snd π ι (genericPoint _) = genericPoint _` using `ι.isOpenEmbedding.injective (by`. Rewrite using `[← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, e₁, h, e₀])`. Establish `e₃ : t = genericPoint _` using `ι.isOpenEmbedding.injective (ht.trans e₀.symm)`. Establish `e₄` using `residueDegree_comp (pullback.fst π ι) π (genericPoint _)`.

Rewrite `e₄` using `[pullback.condition, residueDegree_comp, residueDegree_of_isOpenImmersion, residueDegree_of_isOpenImmersion (pullback.fst π ι), e₁, one_mul, mul_one]`. Express the relevant statement in the definitionally equal form `(pullback.snd π ι).appTop.hom.finrank ((Scheme.isoSpec _).hom t) = _`. Rewrite using `[e₃, finrank_appTop_eq _ e₂, e₄]`.
-/
theorem finrank_genericPoint {C' C : Scheme.{0}} [IsIntegral C'] [IsIntegral C] (π : C' ⟶ C)
    [IsAffineHom π] (h : π (genericPoint C') = genericPoint C) :
    π.finrank (genericPoint C) = π.residueDegree (genericPoint C') := by
  let ι := C.affineOpenCover.f (C.affineOpenCover.idx (genericPoint C))
  let t := (C.affineOpenCover.covers (genericPoint C)).choose
  have ht : ι t = genericPoint C := (C.affineOpenCover.covers (genericPoint C)).choose_spec
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := ι) _ t
    (h.trans ht.symm)
  haveI : Nonempty _ := ⟨t⟩
  haveI := isIntegral_of_isOpenImmersion ι
  haveI : Nonempty ↥(pullback π ι) := ⟨y⟩
  haveI := isIntegral_of_isOpenImmersion (pullback.fst π ι)
  haveI : IsAffine (pullback π ι) := isAffine_of_isAffineHom (pullback.snd π ι)
  have e₀ := genericPoint_eq_of_isOpenImmersion ι
  have e₁ := genericPoint_eq_of_isOpenImmersion (pullback.fst π ι)
  have e₂ : pullback.snd π ι (genericPoint _) = genericPoint _ :=
    ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, e₁, h, e₀])
  have e₃ : t = genericPoint _ := ι.isOpenEmbedding.injective (ht.trans e₀.symm)
  have e₄ := residueDegree_comp (pullback.fst π ι) π (genericPoint _)
  rw [pullback.condition, residueDegree_comp, residueDegree_of_isOpenImmersion,
    residueDegree_of_isOpenImmersion (pullback.fst π ι), e₁, one_mul, mul_one] at e₄
  change (pullback.snd π ι).appTop.hom.finrank ((Scheme.isoSpec _).hom t) = _
  rw [e₃, finrank_appTop_eq _ e₂, e₄]

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

variable {C}

end Clauses

end GlobalTheory.CurveDegreesCompare
