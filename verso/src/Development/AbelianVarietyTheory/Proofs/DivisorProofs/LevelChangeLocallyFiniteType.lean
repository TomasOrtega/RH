import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

namespace GlobalTheory.FlatModel

/- English proof (translation)
Take `⟨N, i, hi, -, rfl⟩` from `h`. Establish `: IsProper (PSpace.str R N)` using `isProper_str R N`. Use `infer_instance`.
-/
theorem locallyOfFiniteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsQProjOver f) : LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

/- English proof (translation)
Establish `h1 : ((IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F)).FiniteType`. Establish `: (IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F) = algebraMap ℚ F'` using `RingHom.ext fun _ => by simp`. Rewrite using `[this]`. Conclude with `(RingHom.Finite.finiteType (RingHom.finite_algebraMap.mpr inferInstance))`. Establish `h2` using `RingHom.FiniteType.of_comp_finiteType h1`.

Conclude with `HasRingHomProperty.Spec_iff.mpr h2`.
-/
theorem locallyOfFiniteType_spMap_inclusion {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F']
    (hle : F ≤ F') : LocallyOfFiniteType (spMap (IntermediateField.inclusion hle).toRingHom) := by
  have h1 : ((IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F)).FiniteType := by
    have : (IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F) = algebraMap ℚ F' :=
      RingHom.ext fun _ => by simp
    rw [this]
    exact (RingHom.Finite.finiteType (RingHom.finite_algebraMap.mpr inferInstance))
  have h2 := RingHom.FiniteType.of_comp_finiteType h1
  exact HasRingHomProperty.Spec_iff.mpr h2

/- English proof (translation)
Introduce `E _ _ _ H Dw l l' Xo Xo' c c' r hle h`. Use `haveI : FiniteDimensional ℚ c'.F := c'.fin`. Use `haveI := locallyOfFiniteType_of_isQProjOver Xo'.qproj`. Use `haveI := locallyOfFiniteType_spMap_inclusion hle`. Use `haveI : LocallyOfFiniteType (r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by`.

Rewrite using `[h]`. Use `infer_instance`. Conclude with `locallyOfFiniteType_of_comp r (pullback.snd _ _)`.
-/
theorem locallyOfFiniteType_of_overIncl : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), GlobalTheory.FlatModel.OverIncl r hle → LocallyOfFiniteType r := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' r hle h
  haveI : FiniteDimensional ℚ c'.F := c'.fin
  haveI := locallyOfFiniteType_of_isQProjOver Xo'.qproj
  haveI := locallyOfFiniteType_spMap_inclusion hle
  haveI : LocallyOfFiniteType (r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [h]; infer_instance
  exact locallyOfFiniteType_of_comp r (pullback.snd _ _)

end GlobalTheory.FlatModel
