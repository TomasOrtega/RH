import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

/- English proof (translation)
Introduce `U X c _ _ K _ y`. Use `set P := pullback y c`. Use `haveI : IsAffine P := inferInstance`. Set `f : P ⟶ Sp K` to `pullback.fst y c`. Set `A : CommRingCat` to `Γ(P, ⊤)`.

Set `φ : CommRingCat.of K ⟶ A` to `Spec.preimage (P.isoSpec.inv ≫ f)`. Establish `hφ : Spec.map φ = P.isoSpec.inv ≫ f` using `Spec.map_preimage _`. Use `haveI : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance`. Establish `hfin : φ.hom.Finite` using `(IsFinite.SpecMap_iff φ).mp inferInstance`. Take `⟨p, -⟩` from `(pullback.fst y c).surjective (IsLocalRing.closedPoint K)`.

Use `haveI : Nontrivial A := by`. Establish `q : PrimeSpectrum A` using `P.isoSpec.hom.base p`. Conclude with `q.nontrivial`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (A : Type)`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`.

Use `letI : Algebra K A := φ.hom.toAlgebra`. Use `haveI : Module.Finite K A := hfin`. Use `haveI : Module.Finite K (A ⧸ m) := Module.Finite.trans A (A ⧸ m)`. Use `⟨A ⧸ m, inferInstance, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ P.isoSpec.inv ≫ pullback.snd y c, ?_⟩` and prove the remaining obligations. Simplify using `only [Category.assoc]`.

Rewrite using `[← pullback.condition, ← Category.assoc P.isoSpec.inv, ← hφ, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem lift_fieldPoint : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  intro U X c _ _ K _ y
  set P := pullback y c
  haveI : IsAffine P := inferInstance
  let f : P ⟶ Sp K := pullback.fst y c
  let A : CommRingCat := Γ(P, ⊤)
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (P.isoSpec.inv ≫ f)
  have hφ : Spec.map φ = P.isoSpec.inv ≫ f := Spec.map_preimage _
  haveI : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance

  obtain ⟨p, -⟩ := (pullback.fst y c).surjective (IsLocalRing.closedPoint K)
  haveI : Nontrivial A := by
    have q : PrimeSpectrum A := P.isoSpec.hom.base p
    exact q.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A : Type)
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Module.Finite K A := hfin
  haveI : Module.Finite K (A ⧸ m) := Module.Finite.trans A (A ⧸ m)
  refine ⟨A ⧸ m, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ P.isoSpec.inv ≫ pullback.snd y c, ?_⟩
  simp only [Category.assoc]
  rw [← pullback.condition, ← Category.assoc P.isoSpec.inv, ← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift
