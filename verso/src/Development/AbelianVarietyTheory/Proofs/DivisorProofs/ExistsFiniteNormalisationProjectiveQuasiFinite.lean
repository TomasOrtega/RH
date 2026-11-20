import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

/- English proof (translation)
Establish `hc : IsClosed (closedPoints T)`. Rewrite using `[← Set.biUnion_of_singleton (closedPoints T)]`. Conclude with `h.isClosed_biUnion fun x hx ↦ hx`. Establish `e` using `JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := T))`. Rewrite `e` using `[Set.univ_inter, hc.closure_eq]`.

Rewrite using `[← Set.finite_univ_iff, ← e]`. Conclude with `h`.
-/
theorem finite_of_finite_closedPoints {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (h : (closedPoints T).Finite) : Finite T := by
  have hc : IsClosed (closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx
  have e := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := T))
  rw [Set.univ_inter, hc.closure_eq] at e
  rw [← Set.finite_univ_iff, ← e]
  exact h

/- English proof (translation)
Establish `: LocallyOfFiniteType (f.fiberToSpecResidueField y)` using `by show LocallyOfFiniteType (pullback.snd _ _); infer_instance`. Use `isClosed_singleton_iff_isClosedImmersion.mp hz` as an intermediate fact. Take `⟨ψ, hψ⟩` from `Spec.map_surjective ((f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y)`. Establish `h1 : LocallyOfFiniteType (Spec.map ψ)` using `hψ ▸ inferInstance`. Establish `h2 : IsFinite (Spec.map ψ)` using `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr h1`.

Rewrite `h2` using `[IsFinite.SpecMap_iff]`. Use `letI := ψ.hom.toAlgebra`. Use `haveI : Module.Finite (Y.residueField y) ((f.fiber y).residueField z) := h2`. Set `σ : (f.fiber y).residueField z →ₐ[Y.residueField y] AlgebraicClosure (Y.residueField y)` to `IsAlgClosed.lift`. Use `⟨CommRingCat.ofHom σ.toRingHom, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hψ]`. Use `(Spec.map_comp _ _).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `a`. Conclude with `σ.commutes a`.
-/
theorem exists_embedding_closedPoint_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (hz : IsClosed ({z} : Set (f.fiber y))) :
    ∃ σ : (f.fiber y).residueField z ⟶ CommRingCat.of (AlgebraicClosure (Y.residueField y)),
      Spec.map σ ≫ (f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have := isClosed_singleton_iff_isClosedImmersion.mp hz
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    ((f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := hψ ▸ inferInstance
  have h2 : IsFinite (Spec.map ψ) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr h1
  rw [IsFinite.SpecMap_iff] at h2
  letI := ψ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField y) ((f.fiber y).residueField z) := h2
  let σ : (f.fiber y).residueField z →ₐ[Y.residueField y] AlgebraicClosure (Y.residueField y) :=
    IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  rw [← hψ]
  refine (Spec.map_comp _ _).symm.trans ?_
  congr 1
  ext a
  exact σ.commutes a

/- English proof (translation)
Set `K` to `AlgebraicClosure (Y.residueField y)`. Use `choose σ hσ using exists_embedding_closedPoint_fiber f y`. Set `Φ : closedPoints (f.fiber y) → (Sp K ⟶ X)` to `fun z ↦ Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y`. Establish `hΦf (z) : Φ z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y`. Simplify using `only [Φ, Category.assoc, Scheme.Hom.fiber_fac]`.

Rewrite using `[← hσ z.1 z.2]`. Simplify using `only [Category.assoc]`. Establish `hΦpt (z) : Φ z (IsLocalRing.closedPoint K : Sp K) = f.fiberι y z.1`. Establish `hm : (f.fiber y).fromSpecResidueField z.1 (Spec.map (σ z.1 z.2) (IsLocalRing.closedPoint K : Sp K)) ∈ Set.range ((f.fiber y).fromSpecResidueField z.1)` using `⟨_, rfl⟩`. Rewrite `hm` using `[Scheme.range_fromSpecResidueField]`.

Use `show (Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y) (IsLocalRing.closedPoint K : Sp K) = _`. Conclude with `congrArg (f.fiberι y) (Set.mem_singleton_iff.mp hm)`. Establish `hΦinj : Function.Injective Φ`. Introduce `z z' h`. Use `hΦpt z` as an intermediate fact.

Rewrite `this` using `[h, hΦpt z']`. Conclude with `Subtype.ext ((f.fiberι y).isEmbedding.injective this).symm`. Establish `hcp : (closedPoints (f.fiber y)).Finite`. Break down `(closedPoints (f.fiber y)).eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩` into its components or cases. Rewrite using `[he]`.

Conclude with `Set.finite_empty`. Establish `hS` using `hf K (Φ ⟨z₀, hz₀⟩) haveI := hS.to_subtype`. Establish `: Finite (closedPoints (f.fiber y))` using `Finite.of_injective (β := {w : Sp K ⟶ X | w ≫ f = Φ ⟨z₀, hz₀⟩ ≫ f}) (fun z ↦ ⟨Φ z, by simp only [Set.mem_setOf_eq, hΦf]⟩) (fun a b h ↦ hΦinj (congrArg Subtype.val h))`. Conclude with `Set.toFinite _`. Use `haveI := finite_of_finite_closedPoints hcp`.

Conclude with `Set.finite_coe_iff.mp ((f.fiberHomeo y).finite_iff.mp inferInstance)`.
-/
theorem finite_preimage_singleton_of_qFin {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : QFin f) (y : Y) : (f ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.residueField y)
  choose σ hσ using exists_embedding_closedPoint_fiber f y
  let Φ : closedPoints (f.fiber y) → (Sp K ⟶ X) := fun z ↦
    Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y
  have hΦf (z) : Φ z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
      Y.fromSpecResidueField y := by
    simp only [Φ, Category.assoc, Scheme.Hom.fiber_fac]
    rw [← hσ z.1 z.2]
    simp only [Category.assoc]
  have hΦpt (z) : Φ z (IsLocalRing.closedPoint K : Sp K) = f.fiberι y z.1 := by
    have hm : (f.fiber y).fromSpecResidueField z.1 (Spec.map (σ z.1 z.2)
        (IsLocalRing.closedPoint K : Sp K)) ∈ Set.range ((f.fiber y).fromSpecResidueField z.1) :=
      ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hm
    show (Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y)
      (IsLocalRing.closedPoint K : Sp K) = _
    exact congrArg (f.fiberι y) (Set.mem_singleton_iff.mp hm)
  have hΦinj : Function.Injective Φ := by
    intro z z' h
    have := hΦpt z
    rw [h, hΦpt z'] at this
    exact Subtype.ext ((f.fiberι y).isEmbedding.injective this).symm
  have hcp : (closedPoints (f.fiber y)).Finite := by
    rcases (closedPoints (f.fiber y)).eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩
    · rw [he]; exact Set.finite_empty
    · have hS := hf K (Φ ⟨z₀, hz₀⟩)
      haveI := hS.to_subtype
      have : Finite (closedPoints (f.fiber y)) :=
        Finite.of_injective (β := {w : Sp K ⟶ X | w ≫ f = Φ ⟨z₀, hz₀⟩ ≫ f})
          (fun z ↦ ⟨Φ z, by simp only [Set.mem_setOf_eq, hΦf]⟩)
          (fun a b h ↦ hΦinj (congrArg Subtype.val h))
      exact Set.toFinite _
  haveI := finite_of_finite_closedPoints hcp
  exact Set.finite_coe_iff.mp ((f.fiberHomeo y).finite_iff.mp inferInstance)

/- English proof (translation)
Introduce `o _ _ _ N X s f hX hN _ _ _ hfs hq`. Substitute `hfs` using the available equality. Use `haveI := isProper_str o N`. Use `haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str o N)`. Use `haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o N)`.

Use `haveI : IsSeparated f := IsSeparated.of_comp f (PSpace.str o N)`. Use `haveI : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (finite_preimage_singleton_of_qFin f hq)`. Conclude with `GlobalTheory.ZMain.exists_finite_openImmersion_pSpace o N X f hX hN inferInstance inferInstance inferInstance inferInstance`.
-/
theorem exists_finite_openImmersion_of_qFin : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  intro o _ _ _ N X s f hX hN _ _ _ hfs hq
  subst hfs
  haveI := isProper_str o N
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str o N)
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o N)
  haveI : IsSeparated f := IsSeparated.of_comp f (PSpace.str o N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (finite_preimage_singleton_of_qFin f hq)
  exact GlobalTheory.ZMain.exists_finite_openImmersion_pSpace o N X f hX hN inferInstance inferInstance
    inferInstance inferInstance

end GlobalTheory.SiegMin
