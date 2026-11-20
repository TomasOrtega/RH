import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.BT

/- English proof (translation)
Introduce `R _ _ T _ Γ`. Establish `hqf : LocallyQuasiFinite Γ.G.hom` using `Γ.quasiFinite`. Establish `hqc : QuasiCompact Γ.G.hom` using `Γ.quasiCompact`. Set `F` to `pullback Γ.G.hom (genPt R).hom`. Set `g : F ⟶ Spec (CommRingCat.of (FractionRing R))` to `pullback.snd Γ.G.hom (genPt R).hom`.

Establish `hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v` using `fun u v => Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v`. Set `b : Spec (CommRingCat.of (FractionRing R))` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))`. Establish `hgqf : LocallyQuasiFinite g` using `inferInstance`. Establish `hgqc : QuasiCompact g` using `inferInstance`. Establish `huniv : g ⁻¹' {b} = Set.univ`.

Use extensionality with `x`. Simplify using `[hK (g x) b]`. Establish `hfin : Finite F`. Establish `h` using `g.finite_preimage_singleton b`. Rewrite `h` using `[huniv]`.

Conclude with `Set.finite_univ_iff.mp h`. Establish `hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom` using `fun t => by`. Rewrite using `[Category.id_comp]`. Conclude with `Over.w (Γ.pt t)`. Set `f : T → F` to `fun t => (pullback.lift _ _ (hw t)) b`.

Use `Finite.of_injective f ?_` and prove the remaining obligations. Introduce `s t hst`. Establish `h` using `congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst`. Simplify using `only [f] at h`. Rewrite `h` using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst]`.

Conclude with `Γ.pt_inj s t b b h`.
-/
theorem QFGroup.finite_of_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  intro R _ _ T _ Γ
  have hqf : LocallyQuasiFinite Γ.G.hom := Γ.quasiFinite
  have hqc : QuasiCompact Γ.G.hom := Γ.quasiCompact
  let F := pullback Γ.G.hom (genPt R).hom
  let g : F ⟶ Spec (CommRingCat.of (FractionRing R)) := pullback.snd Γ.G.hom (genPt R).hom
  have hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v := fun u v =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v
  let b : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  have hgqf : LocallyQuasiFinite g := inferInstance
  have hgqc : QuasiCompact g := inferInstance
  have huniv : g ⁻¹' {b} = Set.univ := by
    ext x; simp [hK (g x) b]
  have hfin : Finite F := by
    have h := g.finite_preimage_singleton b
    rw [huniv] at h
    exact Set.finite_univ_iff.mp h
  have hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom := fun t => by
    rw [Category.id_comp]; exact Over.w (Γ.pt t)
  let f : T → F := fun t => (pullback.lift _ _ (hw t)) b
  refine Finite.of_injective f ?_
  intro s t hst
  have h := congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst
  simp only [f] at h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at h
  exact Γ.pt_inj s t b b h

end GlobalTheory.CompanionTheory.Ar.BT
