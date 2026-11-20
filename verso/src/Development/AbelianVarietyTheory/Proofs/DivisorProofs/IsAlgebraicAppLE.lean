import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.GenDegAlg

/- English proof (translation)
Introduce `X Y _ _ π hgen hdeg U V hU hV h`. Establish `hη : genericPoint Y ∈ V` using `((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)`. Establish `hx : π (genericPoint Y) ∈ U` using `h hη`. Use `letI : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V h).hom.toAlgebra`. Use `letI : Algebra Γ(X, U) (X.residueField (π (genericPoint Y))) := (X.evaluation U _ hx).hom.toAlgebra`.

Use `letI : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra`. Use `letI : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) := (Y.evaluation V _ hη).hom.toAlgebra`. Use `letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) := (X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)).hom.toAlgebra`. Use `haveI : IsScalarTower Γ(X, U) (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' rfl`. Establish `hnat : π.appLE U V h ≫ Y.evaluation V _ hη = X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)`.

Rewrite using `[Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]`. Use `congr 1`. Simplify using `[Scheme.evaluation]`. Use `haveI : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm`. Use `haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU hgen hx`.

Use `haveI : Nonempty U := ⟨⟨_, hx⟩⟩`. Use `haveI : Module.Finite (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)`. Use `haveI : Algebra.IsAlgebraic (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) := Algebra.IsAlgebraic.of_finite _ _`. Use `haveI : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) := (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (π (genericPoint Y)))).2 inferInstance`. Establish `hinj : Function.Injective (Y.evaluation V _ hη).hom`.

Establish `h1` using `germ_injective_of_isIntegral Y (genericPoint Y) hη`. Establish `h2 : Function.Injective (Y.residue (genericPoint Y)).hom` using `RingHom.injective (show Y.functionField →+* Y.residueField (genericPoint Y) from (Y.residue (genericPoint Y)).hom)`. Conclude with `h2.comp h1`. Conclude with `Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y))) hinj`.
-/
theorem isAlgebraic_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (letI := (π.appLE U V h).hom.toAlgebra; Algebra.IsAlgebraic Γ(X, U) Γ(Y, V)) := by
  intro X Y _ _ π hgen hdeg U V hU hV h
  have hη : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hx : π (genericPoint Y) ∈ U := h hη
  letI : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V h).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.residueField (π (genericPoint Y))) :=
    (X.evaluation U _ hx).hom.toAlgebra
  letI : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hη).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' rfl
  have hnat : π.appLE U V h ≫ Y.evaluation V _ hη =
      X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y) := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  haveI : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU hgen hx
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  haveI : Module.Finite (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  haveI : Algebra.IsAlgebraic (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (π (genericPoint Y)))).2 inferInstance
  have hinj : Function.Injective (Y.evaluation V _ hη).hom := by
    have h1 := germ_injective_of_isIntegral Y (genericPoint Y) hη
    have h2 : Function.Injective (Y.residue (genericPoint Y)).hom :=
      RingHom.injective (show Y.functionField →+* Y.residueField (genericPoint Y) from
        (Y.residue (genericPoint Y)).hom)
    exact h2.comp h1
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V)
    (Y.residueField (genericPoint Y))) hinj

end GlobalTheory.GenDegAlg
