import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ClosedPts

/- English proof (translation)
Introduce `k _ _ Z s _ hfin z`. Use `haveI : JacobsonSpace (Sp k) := (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace (R := k)).mp inferInstance`. Use `haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace s`. Set `pt : Sp k` to `IsLocalRing.closedPoint (CommRingCat.of k)`. Establish `hsec : ∀ x : Z, IsClosed ({x} : Set Z) → x ∈ (fun σ : Sp k ⟶ Z => σ pt) '' {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _}`.

Introduce `x hx`. Use `haveI := (isClosed_singleton_iff_locallyOfFiniteType (x := x)).mp hx`. Take `⟨g, hg⟩ : ∃ g : CommRingCat.of k ⟶ Z.residueField x, Spec.map g = Z.fromSpecResidueField x ≫ s` from `⟨Spec.preimage (Z.fromSpecResidueField x ≫ s), Spec.map_preimage _⟩`. Establish `hlft : LocallyOfFiniteType (Spec.map g)` using `by rw [hg]; infer_instance`. Establish `hft : g.hom.FiniteType` using `HasRingHomProperty.Spec_iff.mp hlft`.

Use `letI : Algebra k (Z.residueField x) := g.hom.toAlgebra`. Use `haveI : Algebra.FiniteType k (Z.residueField x) := hft`. Use `haveI : Module.Finite k (Z.residueField x) := finite_of_finite_type_of_isJacobsonRing k _`. Establish `hbij : Function.Bijective (algebraMap k (Z.residueField x))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e` to `RingEquiv.ofBijective (algebraMap k (Z.residueField x)) hbij`.

Set `φ : Z.residueField x ⟶ CommRingCat.of k` to `CommRingCat.ofHom e.symm.toRingHom`. Establish `hgφ : g ≫ φ = 𝟙 _`. Use extensionality with `a`. Conclude with `e.symm_apply_apply a`. Use `⟨Spec.map φ ≫ Z.fromSpecResidueField x, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : (Spec.map φ ≫ Z.fromSpecResidueField x) ≫ s = Spec.map (g ≫ φ)`. Rewrite using `[Category.assoc, ← hg]`. Conclude with `(Spec.map_comp _ _).symm`. Rewrite `h1` using `[hgφ, Spec.map_id]`. Conclude with `h1`.

Simplify using `[Scheme.fromSpecResidueField_apply]`. Establish `hcp : (closedPoints Z).Finite` using `(hfin.image (fun σ : Sp k ⟶ Z => σ pt)).subset (fun x hx => hsec x hx)`. Establish `hT : (closure ({z} : Set Z) ∩ closedPoints Z).Finite` using `hcp.subset Set.inter_subset_right`. Establish `hTc : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z)`. Rewrite using `[← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]`.

Conclude with `hT.isClosed_biUnion (fun t ht => ht.2)`. Establish `heq : closure (closure ({z} : Set Z) ∩ closedPoints Z) = closure ({z} : Set Z)` using `JacobsonSpace.closure_inter_closedPoints isClosed_closure`. Establish `hz : z ∈ closure ({z} : Set Z) ∩ closedPoints Z`. Rewrite using `[← hTc.closure_eq, heq]`. Conclude with `subset_closure (Set.mem_singleton z)`.

Conclude with `hz.2`.
-/
theorem isClosed_singleton_of_finite_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (Z : Scheme.{0}) (s : Z ⟶ Sp k) [LocallyOfFiniteType s], Set.Finite {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} → ∀ z : Z, IsClosed ({z} : Set Z) := by
  intro k _ _ Z s _ hfin z
  haveI : JacobsonSpace (Sp k) :=
    (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace (R := k)).mp inferInstance
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace s
  let pt : Sp k := IsLocalRing.closedPoint (CommRingCat.of k)
  have hsec : ∀ x : Z, IsClosed ({x} : Set Z) →
      x ∈ (fun σ : Sp k ⟶ Z => σ pt) '' {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} := by
    intro x hx
    haveI := (isClosed_singleton_iff_locallyOfFiniteType (x := x)).mp hx
    obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of k ⟶ Z.residueField x,
        Spec.map g = Z.fromSpecResidueField x ≫ s :=
      ⟨Spec.preimage (Z.fromSpecResidueField x ≫ s), Spec.map_preimage _⟩
    have hlft : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff.mp hlft
    letI : Algebra k (Z.residueField x) := g.hom.toAlgebra
    haveI : Algebra.FiniteType k (Z.residueField x) := hft
    haveI : Module.Finite k (Z.residueField x) := finite_of_finite_type_of_isJacobsonRing k _
    have hbij : Function.Bijective (algebraMap k (Z.residueField x)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := RingEquiv.ofBijective (algebraMap k (Z.residueField x)) hbij
    let φ : Z.residueField x ⟶ CommRingCat.of k := CommRingCat.ofHom e.symm.toRingHom
    have hgφ : g ≫ φ = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    refine ⟨Spec.map φ ≫ Z.fromSpecResidueField x, ?_, ?_⟩
    · have h1 : (Spec.map φ ≫ Z.fromSpecResidueField x) ≫ s = Spec.map (g ≫ φ) := by
        rw [Category.assoc, ← hg]
        exact (Spec.map_comp _ _).symm
      rw [hgφ, Spec.map_id] at h1
      exact h1
    · simp [Scheme.fromSpecResidueField_apply]
  have hcp : (closedPoints Z).Finite :=
    (hfin.image (fun σ : Sp k ⟶ Z => σ pt)).subset (fun x hx => hsec x hx)
  have hT : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
    hcp.subset Set.inter_subset_right
  have hTc : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
    rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
    exact hT.isClosed_biUnion (fun t ht => ht.2)
  have heq : closure (closure ({z} : Set Z) ∩ closedPoints Z) = closure ({z} : Set Z) :=
    JacobsonSpace.closure_inter_closedPoints isClosed_closure
  have hz : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
    rw [← hTc.closure_eq, heq]
    exact subset_closure (Set.mem_singleton z)
  exact hz.2

end GlobalTheory.CompanionTheory.ClosedPts
