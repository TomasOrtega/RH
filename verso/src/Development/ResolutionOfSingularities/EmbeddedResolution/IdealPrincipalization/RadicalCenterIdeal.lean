import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Introduce `x hx`. Take `⟨n, hn⟩` from `hx`. Rewrite `hn` using `[RingHom.mem_ker, map_pow]`. Rewrite using `[RingHom.mem_ker]`. Conclude with `IsNilpotent.eq_zero ⟨n, hn⟩`.
-/
private theorem radical_ker_le_ker_of_isReduced {R S : Type*} [CommRing R] [CommRing S] [IsReduced S]
    (f : R →+* S) : (RingHom.ker f).radical ≤ RingHom.ker f := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker, map_pow] at hn
  rw [RingHom.mem_ker]
  exact IsNilpotent.eq_zero ⟨n, hn⟩

/- English proof (translation)
Introduce `k ik X p Z ism J hsub`. Establish `hstalk : ∀ x : ↥Z.subscheme, _root_.IsReduced ↑(Z.subscheme.presheaf.stalk x)`. Introduce `x`. Use `isDomain_stalk_of_smooth (Z.subschemeι ≫ p) x` as an intermediate fact. Use `infer_instance`.

Establish `hred : AlgebraicGeometry.IsReduced Z.subscheme` using `isReduced_of_isReduced_stalk Z.subscheme`. Establish `hcomp : ∀ U : Z.subscheme.Opens, _root_.IsReduced ↑(Z.subscheme.presheaf.obj (Opposite.op U))` using `fun U => AlgebraicGeometry.IsReduced.component_reduced U`. Establish `hZrad : ∀ U : X.affineOpens, (Z.ideal U).radical ≤ Z.ideal U`. Introduce `U`. Rewrite using `[← Z.ker_subschemeι_app U]`.

Conclude with `radical_ker_le_ker_of_isReduced _`. Establish `hle : Z.support ≤ J.support` using `SetLike.coe_subset_coe.mp hsub`. Establish `hJv : J ≤ Scheme.IdealSheafData.vanishingIdeal Z.support`. Apply `(Scheme.IdealSheafData.gc J Z.support).mp` to reduce the goal to its premises. Conclude with `hle`.

Rewrite `hJv` using `[Scheme.IdealSheafData.vanishingIdeal_support]`. Establish `hrad : Z.radical ≤ Z`. Rewrite using `[Scheme.IdealSheafData.le_def]`. Introduce `U`. Rewrite using `[Scheme.IdealSheafData.radical_ideal]`.

Conclude with `hZrad U`. Conclude with `le_trans hJv hrad`.
-/
theorem smoothSubschemeIdealIsRadical : SmoothSubschemeIdealIsRadical.{u} := by
  intro k ik X p Z ism J hsub
  have hstalk : ∀ x : ↥Z.subscheme, _root_.IsReduced ↑(Z.subscheme.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth (Z.subschemeι ≫ p) x
    infer_instance
  have hred : AlgebraicGeometry.IsReduced Z.subscheme :=
    isReduced_of_isReduced_stalk Z.subscheme
  have hcomp : ∀ U : Z.subscheme.Opens,
      _root_.IsReduced ↑(Z.subscheme.presheaf.obj (Opposite.op U)) :=
    fun U => AlgebraicGeometry.IsReduced.component_reduced U
  have hZrad : ∀ U : X.affineOpens, (Z.ideal U).radical ≤ Z.ideal U := by
    intro U
    rw [← Z.ker_subschemeι_app U]
    exact radical_ker_le_ker_of_isReduced _
  have hle : Z.support ≤ J.support := SetLike.coe_subset_coe.mp hsub
  have hJv : J ≤ Scheme.IdealSheafData.vanishingIdeal Z.support := by
    apply (Scheme.IdealSheafData.gc J Z.support).mp
    exact hle
  rw [Scheme.IdealSheafData.vanishingIdeal_support] at hJv
  have hrad : Z.radical ≤ Z := by
    rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [Scheme.IdealSheafData.radical_ideal]
    exact hZrad U
  exact le_trans hJv hrad

end FunctorialResolution.EmbeddedResolution
