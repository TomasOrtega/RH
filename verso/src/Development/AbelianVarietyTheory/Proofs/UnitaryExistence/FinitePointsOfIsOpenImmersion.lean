import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsionStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

namespace GlobalTheory.AbelianSubgroupFinite

/- English proof (translation)
Set `pt : Sp k` to `IsLocalRing.closedPoint k`. Set `F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left` to `fun x => x.left pt`. Set `φ : (𝟙_ (Over (Sp k)) ⟶ N) → (N₀ ⟶ N)` to `fun x => ν ≫ (GrpObj.mulRight x).hom`. Establish `hφ : ∀ x, IsOpenImmersion (φ x).left` using `fun x => by`. Establish `: IsIso (GrpObj.mulRight x).hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))`.

Simplify using `only [φ, Over.comp_left]`. Use `infer_instance`. Establish `hx : ∀ x, e ≫ φ x = x` using `fun x => by`. Simplify using `only [φ]`. Rewrite using `[← Category.assoc, he]`.

Simplify `lift_comp_one_left (𝟙 _) x` using `[comp_lift_assoc]`. Take `⟨t, ht⟩` from `(NoetherianSpace.isCompact (Set.range F)).elim_finite_subcover (fun x => Set.range (φ x).left) (fun x => (φ x).left.isOpenEmbedding.isOpen_range) (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `Set.mem_iUnion.2 ⟨x, e.left pt, ?_⟩` and prove the remaining obligations. Simplify using `only [F]`.

Use `conv_rhs => rw [← hx x]`. Simplify using `only [Over.comp_left, Scheme.Hom.comp_apply])`. Use `Finite.of_surjective (fun p : t × (𝟙_ (Over (Sp k)) ⟶ N₀) => p.2 ≫ φ p.1.1) fun y => ?_` and prove the remaining obligations. Take `⟨x, hxt, hy⟩` from `Set.mem_iUnion₂.1 (ht ⟨y, rfl⟩)`. Establish `hsub : Set.range y.left ⊆ Set.range (φ x).left`.

Introduce and unpack `_ ⟨a, rfl⟩`. Establish `: Subsingleton (Sp k)` using `inferInstance`. Rewrite using `[show a = pt from this.elim _ _]`. Conclude with `hy`. Use `⟨⟨⟨x, hxt⟩, Over.homMk (IsOpenImmersion.lift (φ x).left y.left hsub) ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← (φ x).w, IsOpenImmersion.lift_fac_assoc, y.w]`. Conclude with `Over.OverMorphism.ext (IsOpenImmersion.lift_fac (φ x).left y.left hsub)`.
-/
theorem finite_points_of_isOpenImmersion {k : Type} [Field k] [IsAlgClosed k]
    (N : Over (Sp k)) [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    {N₀ : Over (Sp k)} (ν : N₀ ⟶ N) [IsOpenImmersion ν.left] (e : 𝟙_ (Over (Sp k)) ⟶ N₀)
    (he : e ≫ ν = η[N]) [Finite (𝟙_ (Over (Sp k)) ⟶ N₀)] : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  let φ : (𝟙_ (Over (Sp k)) ⟶ N) → (N₀ ⟶ N) := fun x => ν ≫ (GrpObj.mulRight x).hom
  have hφ : ∀ x, IsOpenImmersion (φ x).left := fun x => by
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    simp only [φ, Over.comp_left]
    infer_instance
  have hx : ∀ x, e ≫ φ x = x := fun x => by
    simp only [φ]
    rw [← Category.assoc, he]
    simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_finite_subcover
    (fun x => Set.range (φ x).left) (fun x => (φ x).left.isOpenEmbedding.isOpen_range) (by
      rintro _ ⟨x, rfl⟩
      refine Set.mem_iUnion.2 ⟨x, e.left pt, ?_⟩
      simp only [F]
      conv_rhs => rw [← hx x]
      simp only [Over.comp_left, Scheme.Hom.comp_apply])
  refine Finite.of_surjective
    (fun p : t × (𝟙_ (Over (Sp k)) ⟶ N₀) => p.2 ≫ φ p.1.1) fun y => ?_
  obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht ⟨y, rfl⟩)
  have hsub : Set.range y.left ⊆ Set.range (φ x).left := by
    rintro _ ⟨a, rfl⟩
    have : Subsingleton (Sp k) := inferInstance
    rw [show a = pt from this.elim _ _]
    exact hy
  refine ⟨⟨⟨x, hxt⟩, Over.homMk (IsOpenImmersion.lift (φ x).left y.left hsub) ?_⟩, ?_⟩
  · rw [← (φ x).w, IsOpenImmersion.lift_fac_assoc, y.w]
  · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac (φ x).left y.left hsub)

/- English proof (translation)
Introduce `k _ _ B _ n hB hn hnk C Z hZ hC htor`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.comm` as an intermediate fact. Take `⟨N, _, ν, hν, hνc, hNs, hr⟩` from `GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC`.

Establish `hNp : IsProper N.hom` using `by rw [← ν.w]; infer_instance`. Take `⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩` from `GlobalTheory.exists_neutralComponent k N hNs inferInstance`. Establish `: IsClosedImmersion (ν₀ ≫ ν).left` using `by rw [Over.comp_left]; infer_instance`. Establish `: Mono (ν₀ ≫ ν)` using `Over.mono_of_mono_left _`. Establish `hA : IsAbelianScheme N₀` using `{ comm := isCommMonObj_of_mono (ν₀ ≫ ν) smooth := SmoothOfRelativeDimension.smooth g N₀.hom proper := by rw [← ν₀.w]; infer_instance geomConnected := hgc }`.

Establish `hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C` using `fun x => by`. Rewrite using `[hC, ← hr]`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨x.left t, rfl⟩`. Establish `hfin₀ : Finite (𝟙_ (Over (Sp k)) ⟶ N₀)`.

Use `GlobalTheory.T.finite_points_abelianVariety_of_no_torsion k N₀ hA n hn.two_le hnk fun x hx => ?_` and prove the remaining obligations. Establish `h2 : x ≫ ν₀ ≫ ν = 1`. Use `htor _ (by rw [← Category.assoc]; exact hmem _) ?_` and prove the remaining obligations. Rewrite using `[← MonObj.pow_comp, hx, MonObj.one_comp]`. Rewrite using `[← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]`.

Establish `: IsLocallyNoetherian N.left` using `LocallyOfFiniteType.isLocallyNoetherian N.hom`. Establish `: CompactSpace N.left` using `QuasiCompact.compactSpace_of_compactSpace N.hom`. Establish `: IsNoetherian N.left` using `{}`. Use `finite_points_of_isOpenImmersion N ν₀ η[N₀] (IsMonHom.one_hom ν₀)` as an intermediate fact. Use `Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_` and prove the remaining obligations.

Introduce and unpack `⟨x, hx⟩`. Establish `: IsReduced (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (IsReduced (Sp k))`. Take `⟨l, hl⟩` from `exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)`. Use `⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩` and prove the remaining obligations. Rewrite using `[← ν.w, ← Category.assoc, hl, x.w]`.
-/
theorem finite_of_torsionFree : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) := by
  intro k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have hfin₀ : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine GlobalTheory.T.finite_points_abelianVariety_of_no_torsion k N₀ hA n hn.two_le hnk fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  have := finite_points_of_isOpenImmersion N ν₀ η[N₀] (IsMonHom.one_hom ν₀)
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

end GlobalTheory.AbelianSubgroupFinite
