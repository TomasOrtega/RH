import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeEqZeroOfSqDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatIffExistsRatFunc

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

namespace SplitTorusRigid

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]`. Both sides reduce to the same expression.
-/
theorem gamma_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (y : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom ((spMap f).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]; rfl

/- English proof (translation)
Establish `h` using `SplitTorus.val_one (T := 𝟙_ (Over S)) (S := S) (X := X) a`. Rewrite `h` using `[SplitTorus.val_eq]`. Establish `e : (1 : 𝟙_ (Over S) ⟶ splitTorus S X) = η[splitTorus S X]`. Rewrite using `[Hom.one_def]`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem unitSec_chi {S : Scheme.{0}} (X : Type) [AddCommGroup X] (a : X) :
    (unitSec (splitTorus S X)).appTop.hom (Rosenlicht.chi X a) = 1 := by
  have h := SplitTorus.val_one (T := 𝟙_ (Over S)) (S := S) (X := X) a
  rw [SplitTorus.val_eq] at h
  have e : (1 : 𝟙_ (Over S) ⟶ splitTorus S X) = η[splitTorus S X] := by
    rw [Hom.one_def]; simp
  rw [e] at h
  exact h

/- English proof (translation)
Establish `h` using `SplitTorus.val_mul (𝟙 (splitTorus S X)) (𝟙 _) a`. Rewrite `h` using `[SplitTorus.val_eq, SplitTorus.val_id]`. Conclude with `h`.
-/
theorem sqr_chi {S : Scheme.{0}} (X : Type) [AddCommGroup X] (a : X) :
    (sqr (splitTorus S X)).appTop.hom (Rosenlicht.chi X a) = Rosenlicht.chi X a * Rosenlicht.chi X a := by
  have h := SplitTorus.val_mul (𝟙 (splitTorus S X)) (𝟙 _) a
  rw [SplitTorus.val_eq, SplitTorus.val_id] at h
  exact h

end SplitTorusRigid

open SplitTorusRigid in

/- English proof (translation)
Introduce `Ω _ _ X _ ξ hξ hr`. Take `⟨β, hβ⟩` from `hr`. Set `φ : X → PowerSeries Ω` to `fun a => (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω))).hom.hom (ξ.appTop.hom (Rosenlicht.chi X a))`. Establish `key : ∀ a, φ a = 1`. Introduce `a`.

Apply `rat_dilation_eq_one Ω (φ a)` to reduce the goal to its premises. Establish `h` using `congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries Ω))).hom.hom (g.appTop.hom (Rosenlicht.chi X a))) hβ`. Rewrite `h` using `[appTop_comp_apply, appTop_comp_apply, gamma_spMap, gamma_spMap]`. Conclude with `(isRat_iff_exists_ratFunc Ω (φ a)).2 ⟨_, h⟩`. Establish `h` using `congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (g.appTop.hom (Rosenlicht.chi X a))) hξ.zero`.

Rewrite `h` using `[appTop_comp_apply, appTop_comp_apply, gamma_spMap, unitSec_chi, map_one, map_one]`. Conclude with `h`. Establish `h` using `congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω))).hom.hom (g.appTop.hom (Rosenlicht.chi X a))) hξ.scale`. Rewrite `h` using `[appTop_comp_apply, appTop_comp_apply, gamma_spMap, sqr_chi, map_mul, map_mul]`. Rewrite using `[h, sq]`.

Establish `hx : ∀ a, ξ.appTop.hom (Rosenlicht.chi X a) = 1` using `fun a => (cr_iso_bij (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω)))).1 (by rw [map_one]; exact key a)`. Establish `ht : ∀ a, (triv (splitTorus (Sp Ω) X) (𝟙 (Sp Ω))).appTop.hom (Rosenlicht.chi X a) = 1`. Introduce `a`. Simplify using `only [triv, appTop_comp_apply, unitSec_chi, map_one]`. Establish `e` using `SplitTorus.hom_ext (g := (Over.homMk ξ hξ.base : Over.mk (spMap (PowerSeries.C (R := Ω)) ≫ 𝟙 (Sp Ω)) ⟶ splitTorus (Sp Ω) X)) (g' := Over.homMk (triv (splitTorus (Sp Ω) X) (𝟙 (Sp Ω))) (triv_over _ _)) (fun a => by rw [SplitTorus.val_eq, SplitTorus.val_eq]; exact (hx a).trans (ht a …`.

Conclude with `congrArg (·.left) e`.
-/
theorem splitTorus_ratRigid : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Type) [AddCommGroup X],
    RatRigid (splitTorus (Sp Ω) X) (𝟙 (Sp Ω)) := by
  intro Ω _ _ X _ ξ hξ hr
  obtain ⟨β, hβ⟩ := hr
  let φ : X → PowerSeries Ω := fun a =>
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω))).hom.hom (ξ.appTop.hom (Rosenlicht.chi X a))
  have key : ∀ a, φ a = 1 := by
    intro a
    apply rat_dilation_eq_one Ω (φ a)
    · have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries Ω))).hom.hom
        (g.appTop.hom (Rosenlicht.chi X a))) hβ
      rw [appTop_comp_apply, appTop_comp_apply, gamma_spMap, gamma_spMap] at h
      exact (isRat_iff_exists_ratFunc Ω (φ a)).2 ⟨_, h⟩
    · have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
        (g.appTop.hom (Rosenlicht.chi X a))) hξ.zero
      rw [appTop_comp_apply, appTop_comp_apply, gamma_spMap, unitSec_chi, map_one, map_one] at h
      exact h
    · have h := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω))).hom.hom
        (g.appTop.hom (Rosenlicht.chi X a))) hξ.scale
      rw [appTop_comp_apply, appTop_comp_apply, gamma_spMap, sqr_chi, map_mul, map_mul] at h
      rw [h, sq]
  have hx : ∀ a, ξ.appTop.hom (Rosenlicht.chi X a) = 1 := fun a =>
    (cr_iso_bij (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries Ω)))).1 (by rw [map_one]; exact key a)
  have ht : ∀ a, (triv (splitTorus (Sp Ω) X) (𝟙 (Sp Ω))).appTop.hom (Rosenlicht.chi X a) = 1 := by
    intro a
    simp only [triv, appTop_comp_apply, unitSec_chi, map_one]
  have e := SplitTorus.hom_ext
    (g := (Over.homMk ξ hξ.base : Over.mk (spMap (PowerSeries.C (R := Ω)) ≫ 𝟙 (Sp Ω)) ⟶ splitTorus (Sp Ω) X))
    (g' := Over.homMk (triv (splitTorus (Sp Ω) X) (𝟙 (Sp Ω))) (triv_over _ _))
    (fun a => by rw [SplitTorus.val_eq, SplitTorus.val_eq]; exact (hx a).trans (ht a).symm)
  exact congrArg (·.left) e

end GlobalTheory.Nef
