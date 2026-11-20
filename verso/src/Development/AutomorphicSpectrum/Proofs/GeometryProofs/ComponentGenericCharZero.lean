import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CharZeroModel

/- English proof (translation)
Use `set x := ξ.base (IsLocalRing.closedPoint Ω) with hx`. Establish `hfl : (s.stalkMap x).hom.Flat` using `Flat.stalkMap s x`. Establish `hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` using `(Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective`. Establish `hgerm` using `germ_injective_of_isIntegral (X := Spec (CommRingCat.of R)) (U := ⊤) (x := s.base x) (hx := trivial)`. Establish `hA : ∀ n : ℕ, n ≠ 0 → (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) ≠ 0`.

Introduce `n hn h0`. Apply `(Nat.cast_ne_zero (R := R)).mpr hn` to reduce the goal to its premises. Apply `hinv` to reduce the goal to its premises. Apply `hgerm` to reduce the goal to its premises. Simplify using `only [map_zero, map_natCast]`.

Conclude with `h0`. Establish `hO : ∀ n : ℕ, n ≠ 0 → (n : X.presheaf.stalk x) ≠ 0`. Introduce `n hn h0`. Set `_` to `(s.stalkMap x).hom.toAlgebra`. Establish `: Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) (X.presheaf.stalk x)` using `hfl`.

Establish `hreg` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x) (mem_nonZeroDivisors_of_ne_zero (hA n hn))`. Establish `h3 : (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (1 : X.presheaf.stalk x) = (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (0 : X.presheaf.stalk x)`. Rewrite using `[smul_zero, Algebra.smul_def, _root_.mul_one, map_natCast]`. Conclude with `h0`. Conclude with `one_ne_zero (hreg h3)`.

Conclude with `charZero_of_inj_zero fun n hn => by`. Assume the negation of the conclusion as `hne`. Apply `hO n hne` to reduce the goal to its premises. Apply `h` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`.

Conclude with `hn`.
-/
theorem charZero_of_flat {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (s : X ⟶ Spec (CommRingCat.of R)) [Flat s] {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : Function.Injective (Scheme.stalkClosedPointTo ξ).hom) : CharZero Ω := by
  classical
  set x := ξ.base (IsLocalRing.closedPoint Ω) with hx
  have hfl : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  have hgerm := germ_injective_of_isIntegral (X := Spec (CommRingCat.of R)) (U := ⊤) (x := s.base x)
    (hx := trivial)
  have hA : ∀ n : ℕ, n ≠ 0 → (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) ≠ 0 := by
    intro n hn h0
    apply (Nat.cast_ne_zero (R := R)).mpr hn
    apply hinv
    apply hgerm
    simp only [map_zero, map_natCast]
    exact h0
  have hO : ∀ n : ℕ, n ≠ 0 → (n : X.presheaf.stalk x) ≠ 0 := by
    intro n hn h0
    let _ := (s.stalkMap x).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) (X.presheaf.stalk x) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
      (mem_nonZeroDivisors_of_ne_zero (hA n hn))
    have h3 : (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (1 : X.presheaf.stalk x) =
        (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (0 : X.presheaf.stalk x) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one, map_natCast]
      exact h0
    exact one_ne_zero (hreg h3)
  exact charZero_of_inj_zero fun n hn => by
    by_contra hne
    apply hO n hne
    apply h
    rw [map_natCast, map_zero]
    exact hn

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ`. Use `Y.flat` as an intermediate fact. Conclude with `charZero_of_flat Y.s ξ₀ hξ.bij.1`.
-/
theorem charZero_function_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  have := Y.flat
  exact charZero_of_flat Y.s ξ₀ hξ.bij.1

end GlobalTheory.CompanionTheory.Ar.CharZeroModel
