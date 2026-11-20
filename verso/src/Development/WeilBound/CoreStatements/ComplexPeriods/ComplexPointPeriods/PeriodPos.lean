import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LocallyQuasiFiniteSpMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xj6.PeriodIn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Use `haveI := Xo.smooth`. Use `haveI hs0 : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s`. Set `s : Xo.XF c ⟶ Sp c.F` to `pullback.snd _ _`. Use `haveI hs : Smooth s := inferInstanceAs (Smooth (pullback.snd _ _))`. Take `⟨L, _, j, g, hj, hg, hZ⟩` from `GlobalTheory.FlatLine.exists_finite_point s hU hne`.

Use `letI : Algebra c.F L := j.toAlgebra`. Use `haveI : Module.Finite c.F L := hj`. Set `e : L →ₐ[c.F] ℂ` to `IsAlgClosed.lift`. Use `⟨spMap e.toRingHom ≫ g, ?_, fun z => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(spMap e.toRingHom ≫ g) ≫ s = _`.

Rewrite using `[Category.assoc, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `e.comp_algebraMap`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hZ _`.
-/
theorem exists_complex_point {U : Set (Xo.XF c)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) ∧ ∀ z, y z ∈ U := by
  haveI := Xo.smooth
  haveI hs0 : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  haveI hs : Smooth s := inferInstanceAs (Smooth (pullback.snd _ _))
  obtain ⟨L, _, j, g, hj, hg, hZ⟩ := GlobalTheory.FlatLine.exists_finite_point s hU hne
  letI : Algebra c.F L := j.toAlgebra
  haveI : Module.Finite c.F L := hj
  let e : L →ₐ[c.F] ℂ := IsAlgClosed.lift
  refine ⟨spMap e.toRingHom ≫ g, ?_, fun z => ?_⟩
  · change (spMap e.toRingHom ≫ g) ≫ s = _
    rw [Category.assoc, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact e.comp_algebraMap
  · rw [Scheme.Hom.comp_apply]; exact hZ _

/- English proof (translation)
Take `⟨y₀, hy₀, hU₀⟩` from `exists_complex_point hU.isOpen hne`. Establish `hs : under y₀ ≫ Xo.s = spMap (algebraMap (KA l) ℂ)`. Rewrite using `[under, Category.assoc, pullback.condition, ← Category.assoc, hy₀, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨i, P₀, hP₀, hu₀⟩` from `FU.onto _ hs`.

Use `⟨i, fun P y hP hu hy => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Establish `h` using `PositivityTheory.Xgn.GeometricOfPeriods.sameComp_periods FU i hty hP hP₀`. Rewrite `h` using `[← hu, hu₀]`. Take `⟨hp, hq, h⟩` from `PositivityTheory.Xgn.GeometricOfPeriods.sameComp_baseChange _ _ Xo.s y y₀ hy hy₀ h`.

Set `π : pullback (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap (algebraMap c.F ℂ)) ⟶ Xo.XF c` to `pullback.fst _ _`. Establish `h1` using `π.continuous.image_connectedComponent_subset _ ⟨_, h z, rfl⟩`. Rewrite `h1` using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst]`. Conclude with `hU.connectedComponent_subset (hU₀ z) h1`.
-/
theorem exists_period {U : Set (Xo.XF c)} (hU : IsClopen U) (hne : U.Nonempty) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (hty : IsTypeFn H D.p D.q ty) :
    ∃ i : Fin FU.n, ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  obtain ⟨y₀, hy₀, hU₀⟩ := exists_complex_point hU.isOpen hne
  have hs : under y₀ ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hy₀, ← Spec.map_comp]; rfl
  obtain ⟨i, P₀, hP₀, hu₀⟩ := FU.onto _ hs
  refine ⟨i, fun P y hP hu hy => ?_⟩
  rintro _ ⟨z, rfl⟩
  have h := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_periods FU i hty hP hP₀
  rw [← hu, hu₀] at h
  obtain ⟨hp, hq, h⟩ := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_baseChange _ _ Xo.s y y₀ hy hy₀ h
  let π : pullback (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (algebraMap c.F ℂ)) ⟶ Xo.XF c := pullback.fst _ _
  have h1 := π.continuous.image_connectedComponent_subset _ ⟨_, h z, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at h1
  exact hU.connectedComponent_subset (hU₀ z) h1

/- English proof (translation)
Take `⟨g, ty, hty⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q`. Take `⟨FU⟩` from `GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo (algebraMap (KA l) ℂ) g ty hr rfl hty`. Take `⟨i, hi⟩` from `exists_period hU hne FU hty`. Conclude with `⟨g, ty, FU, i, hty, hi⟩`.
-/
theorem period_in_pos (hr : 1 ≤ D.p + D.q) {U : Set (Xo.XF c)} (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
      IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
        y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo (algebraMap (KA l) ℂ) g ty hr rfl hty
  obtain ⟨i, hi⟩ := exists_period hU hne FU hty
  exact ⟨g, ty, FU, i, hty, hi⟩

end PositivityTheory.Xj6.PeriodIn
