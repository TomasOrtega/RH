import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

/- English proof (translation)
Use `haveI := D.smooth`. Establish `h` using `HasRingHomProperty.appLE @Smooth D.s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top`. Establish `h' : RingHom.Smooth ((D.s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of D.R)).inv.hom)` using `RingHom.Smooth.comp (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of D.R)).symm.commRingCatIsoToRingEquiv.bijective) h`. Conclude with `RingHom.smooth_algebraMap.mp h'`.
-/
theorem Data.sec_smooth (D : Data) (U : D.X.affineOpens) : Algebra.Smooth D.R (Sec D.s U.1) := by
  haveI := D.smooth
  have h := HasRingHomProperty.appLE @Smooth D.s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((D.s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of D.R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of D.R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

/- English proof (translation)
Take `⟨s₀, hpb, -⟩` from `D.red`. Use `haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `haveI : IsClosedImmersion D.i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip ‹_›`. Use `infer_instance`.
-/
theorem Data.mono_i (D : Data) : Mono D.i := by
  obtain ⟨s₀, hpb, -⟩ := D.red
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion D.i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip ‹_›
  infer_instance

/- English proof (translation)
Use `haveI := D.sep`. Use `haveI : IsSeparated (Limits.terminal.from D.X) := by`. Rewrite using `[← Limits.terminal.comp_from D.s]`. Use `infer_instance`. Conclude with `hU.inf hV`.
-/
theorem Data.affine_inf (D : Data) {U V : D.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  haveI := D.sep
  haveI : IsSeparated (Limits.terminal.from D.X) := by
    rw [← Limits.terminal.comp_from D.s]; infer_instance
  exact hU.inf hV

/- English proof (translation)
The claim follows from `fun D ↦ ⟨D.sec_smooth, D.mono_i, fun _ _ hU hV ↦ D.affine_inf hU hV⟩`.
-/
theorem Data.smooth_mono_inf : ∀ D : Data, (∀ U : D.X.affineOpens, Algebra.Smooth D.R (Sec D.s U.1)) ∧ Mono D.i ∧
    ∀ U V : D.X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
  fun D ↦ ⟨D.sec_smooth, D.mono_i, fun _ _ hU hV ↦ D.affine_inf hU hV⟩

end GlobalTheory.SmoothLift
