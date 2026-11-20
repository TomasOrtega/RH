import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponent

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

namespace GeoD

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Establish `: IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R)` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R)` using `Algebra.FiniteType.of_restrictScalars_finiteType R _ _`. Establish `: IsClosedImmersion (spMap (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)))`. Apply `IsClosedImmersion.spec_of_surjective` to reduce the goal to its premises. Introduce and unpack `⟨p, hp⟩`.

Establish `h0 : p.totalDegree = 0` using `Nat.le_zero.1 (MvPolynomial.IsHomogeneous.totalDegree_le hp)`. Conclude with `⟨p.coeff 0, Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0).symm⟩`. Unfold `PSpace.str`. Use `infer_instance`.
-/
theorem isProper_pspace (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : IsClosedImmersion (spMap (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) := by
    apply IsClosedImmersion.spec_of_surjective
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := Nat.le_zero.1 (MvPolynomial.IsHomogeneous.totalDegree_le hp)
    exact ⟨p.coeff 0, Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0).symm⟩
  unfold PSpace.str
  infer_instance

/- English proof (translation)
Take `⟨N, i, hi, rfl⟩` from `h`. Use `isProper_pspace R N` as an intermediate fact. Conclude with `QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)`.
-/
theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_pspace R N
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

end GeoD

/- English proof (translation)
Introduce `l _ K M hM d hC`. Take `⟨hconn, hsm⟩` from `hC`. Establish `: Smooth M.q` using `SmoothOfRelativeDimension.smooth d M.q`. Establish `: CompactSpace M.X` using `GeoD.compactSpace_of_isProjOver hM.1`. Establish `: QuasiCompact M.p` using `quasiCompact_of_compactSpace M.p`.

Establish `: CompactSpace M.gen` using `inferInstance`. Take `⟨r, U, hint, hcov, hdisj, hperm, htrans⟩` from `GeoC.exists_components (Ω := PadicAlgCl l) M.q`. Establish `hne : ∀ s, (U s : Set (GlobalTheory.Et.geom (PadicAlgCl l) M.q)).Nonempty` using `fun s => by`. Take `⟨⟨y, hy⟩⟩` from `(hint s).nonempty`. Conclude with `⟨y, hy⟩`.

Use `⟨r, fun s => (U s).toScheme, fun s => (U s).ι, ⟨fun s => inferInstance, fun y => ?_, fun s s' h => ?_⟩, hint, fun σ => ?_, fun s s' => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hcov y`. Conclude with `⟨s, by rw [Scheme.Opens.range_ι]; exact hs⟩`. Rewrite using `[Scheme.Opens.range_ι, Scheme.Opens.range_ι]`. Conclude with `hdisj s s' h`.

Use `set g := GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) choose f hf using hperm (IntermediateField.fixingSubgroupEquiv K σ)`. Establish `hginj : Function.Injective g` using `(GeoC.galHomeo M.q (IntermediateField.fixingSubgroupEquiv K σ)).injective`. Establish `hinj : Function.Injective f`. Introduce `s s' hss'`. Assume the negation of the conclusion as `h`.

Establish `h1 : (U s : Set _) = U s'` using `Set.image_injective.2 hginj ((hf s).trans (hss' ▸ (hf s').symm))`. Take `⟨y, hy⟩` from `hne s`. Conclude with `Set.disjoint_left.1 (hdisj s s' h) hy (h1 ▸ hy)`. Set `π` to `Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)`. Establish `hr : ∀ s, Set.range ((U s).ι ≫ g) = Set.range (U (π s)).ι` using `fun s => by`.

Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]`. Conclude with `hf s`. Conclude with `⟨π, fun s => IsOpenImmersion.isoOfRangeEq ((U s).ι ≫ g) (U (π s)).ι (hr s), fun s => (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩`. Take `⟨τ, hτ⟩` from `htrans s s'`. Use `⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩` and prove the remaining obligations.

Rewrite using `[MulEquiv.apply_symm_apply]`. Establish `hr : Set.range ((U s).ι ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ) = Set.range (U s').ι`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]`. Conclude with `hτ`. Conclude with `⟨(IsOpenImmersion.isoOfRangeEq _ _ hr).hom, (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩`.
-/
theorem geoMain : GeometricGenericComponents := by
  intro l _ K M hM d hC
  obtain ⟨hconn, hsm⟩ := hC
  have : Smooth M.q := SmoothOfRelativeDimension.smooth d M.q
  have : CompactSpace M.X := GeoD.compactSpace_of_isProjOver hM.1
  have : QuasiCompact M.p := quasiCompact_of_compactSpace M.p
  have : CompactSpace M.gen := inferInstance
  obtain ⟨r, U, hint, hcov, hdisj, hperm, htrans⟩ := GeoC.exists_components (Ω := PadicAlgCl l) M.q
  have hne : ∀ s, (U s : Set (GlobalTheory.Et.geom (PadicAlgCl l) M.q)).Nonempty := fun s => by
    obtain ⟨⟨y, hy⟩⟩ := (hint s).nonempty
    exact ⟨y, hy⟩
  refine ⟨r, fun s => (U s).toScheme, fun s => (U s).ι, ⟨fun s => inferInstance, fun y => ?_, fun s s' h => ?_⟩,
    hint, fun σ => ?_, fun s s' => ?_⟩
  · obtain ⟨s, hs⟩ := hcov y
    exact ⟨s, by rw [Scheme.Opens.range_ι]; exact hs⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hdisj s s' h
  · set g := GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ)
    choose f hf using hperm (IntermediateField.fixingSubgroupEquiv K σ)
    have hginj : Function.Injective g := (GeoC.galHomeo M.q (IntermediateField.fixingSubgroupEquiv K σ)).injective
    have hinj : Function.Injective f := by
      intro s s' hss'
      by_contra h
      have h1 : (U s : Set _) = U s' :=
        Set.image_injective.2 hginj ((hf s).trans (hss' ▸ (hf s').symm))
      obtain ⟨y, hy⟩ := hne s
      exact Set.disjoint_left.1 (hdisj s s' h) hy (h1 ▸ hy)
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
    have hr : ∀ s, Set.range ((U s).ι ≫ g) = Set.range (U (π s)).ι := fun s => by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hf s
    exact ⟨π, fun s => IsOpenImmersion.isoOfRangeEq ((U s).ι ≫ g) (U (π s)).ι (hr s),
      fun s => (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩
  · obtain ⟨τ, hτ⟩ := htrans s s'
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    have hr : Set.range ((U s).ι ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ) = Set.range (U s').ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hτ
    exact ⟨(IsOpenImmersion.isoOfRangeEq _ _ hr).hom, (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩

end CrystallineSemistableComparison
