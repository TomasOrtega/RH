import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedTorusExtensionOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open Topology TopologicalSpace

namespace GlobalTheory.TorsionDense

open RationalPoint

/- English proof (translation)
Take `⟨E⟩` from `hG.fibres k (𝟙 _)`. Set `e : (Over.pullback (𝟙 (Sp k))).mapMon.obj (Mon.mk G) ≅ Mon.mk G` to `(Functor.mapMonNatIso (Over.pullbackId (X := Sp k)) ≪≫ Functor.mapMonIdIso).app (Mon.mk G)`. Set `e' : (Over.pullback (𝟙 (Sp k))).obj G ≅ G` to `(Mon.forget _).mapIso e`. Establish `: IsMonHom e'.hom`. Express the relevant statement in the definitionally equal form `IsMonHom e.hom.hom`.

Use `infer_instance`. Conclude with `⟨torusExtOfIso e' E⟩`.
-/
theorem nonempty_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (hG : IsSemiAbelian G) : Nonempty (TorusExtension G) := by
  obtain ⟨E⟩ := hG.fibres k (𝟙 _)
  let e : (Over.pullback (𝟙 (Sp k))).mapMon.obj (Mon.mk G) ≅ Mon.mk G :=
    (Functor.mapMonNatIso (Over.pullbackId (X := Sp k)) ≪≫ Functor.mapMonIdIso).app (Mon.mk G)
  let e' : (Over.pullback (𝟙 (Sp k))).obj G ≅ G := (Mon.forget _).mapIso e
  have : IsMonHom e'.hom := by
    change IsMonHom e.hom.hom
    infer_instance
  exact ⟨torusExtOfIso e' E⟩

/- English proof (translation)
Establish `: IsLocallyNoetherian X.left` using `LocallyOfFiniteType.isLocallyNoetherian X.hom`. Establish `: CompactSpace X.left` using `QuasiCompact.compactSpace_of_compactSpace X.hom`. Establish `: IsNoetherian X.left` using `{}`. Use `letI := zariski X`. Conclude with `(IsInducing.induced pt).noetherianSpace`.
-/
theorem noetherianSpace_zariski {k : Type} [Field k] (X : Over (Sp k)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : @NoetherianSpace _ (zariski X) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  letI := zariski X
  exact (IsInducing.induced pt).noetherianSpace

/- English proof (translation)
Use `letI := zariski N`. Use `haveI := separatelyContinuousMul N`. Use `haveI := noetherianSpace_zariski N`. Establish `: LocallyOfFiniteType N₀.hom` using `by rw [← ν.w]; infer_instance`. Set `φ : (𝟙_ (Over (Sp k)) ⟶ N₀) →* (𝟙_ (Over (Sp k)) ⟶ N)` to `MonoidHom.mk' (fun x => x ≫ ν) fun x y => MonObj.mul_comp x y ν`.

Establish `ho : IsOpen (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N))`. Use `isOpen_induced_iff.2 ⟨Set.range ν.left, ν.left.isOpenMap.isOpen_range, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[Set.mem_preimage, ← Set.image_univ, pt_mem_image_iff ν isClosed_univ]`. Conclude with `⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩`.

Establish `hfin : (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)).Finite` using `Set.finite_range φ`. Take `⟨t, ht⟩` from `(NoetherianSpace.isCompact (Set.univ : Set (𝟙_ (Over (Sp k)) ⟶ N))).elim_finite_subcover (fun g : 𝟙_ (Over (Sp k)) ⟶ N => (fun y => g * y) ⁻¹' (φ.range : Set _)) (fun g => ho.preimage (continuous_const_mul g)) (fun y _ => Set.mem_iUnion.2 ⟨y⁻¹, Set.mem_preimage.2 (by rw [inv_mul_ …`. Use `Set.finite_univ_iff.1 (Set.Finite.subset ?_ ht)` and prove the remaining obligations. Conclude with `t.finite_toSet.biUnion fun g _ => hfin.preimage (mul_right_injective g).injOn`.
-/
theorem finite_points_of_isOpenImmersion {k : Type} [Field k] [IsAlgClosed k] {N₀ N : Over (Sp k)}
    [GrpObj N₀] [GrpObj N] [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] (ν : N₀ ⟶ N)
    [IsMonHom ν] [IsOpenImmersion ν.left] [Finite (𝟙_ (Over (Sp k)) ⟶ N₀)] :
    Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  letI := zariski N
  haveI := separatelyContinuousMul N
  haveI := noetherianSpace_zariski N
  have : LocallyOfFiniteType N₀.hom := by rw [← ν.w]; infer_instance
  let φ : (𝟙_ (Over (Sp k)) ⟶ N₀) →* (𝟙_ (Over (Sp k)) ⟶ N) :=
    MonoidHom.mk' (fun x => x ≫ ν) fun x y => MonObj.mul_comp x y ν
  have ho : IsOpen (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)) := by
    refine isOpen_induced_iff.2 ⟨Set.range ν.left, ν.left.isOpenMap.isOpen_range, ?_⟩
    ext y
    rw [Set.mem_preimage, ← Set.image_univ, pt_mem_image_iff ν isClosed_univ]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩
  have hfin : (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)).Finite := Set.finite_range φ
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.univ : Set (𝟙_ (Over (Sp k)) ⟶ N))).elim_finite_subcover
    (fun g : 𝟙_ (Over (Sp k)) ⟶ N => (fun y => g * y) ⁻¹' (φ.range : Set _))
    (fun g => ho.preimage (continuous_const_mul g))
    (fun y _ => Set.mem_iUnion.2 ⟨y⁻¹, Set.mem_preimage.2 (by rw [inv_mul_cancel]; exact φ.range.one_mem)⟩)
  refine Set.finite_univ_iff.1 (Set.Finite.subset ?_ ht)
  exact t.finite_toSet.biUnion fun g _ => hfin.preimage (mul_right_injective g).injOn

/- English proof (translation)
Introduce `k _ _ B _ n hB hn hnk C Z hZ hC htor`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.comm` as an intermediate fact. Take `⟨N, _, ν, hν, hνc, hNs, hr⟩` from `GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC`.

Establish `hNp : IsProper N.hom` using `by rw [← ν.w]; infer_instance`. Take `⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩` from `GlobalTheory.exists_neutralComponent k N hNs inferInstance`. Establish `: IsClosedImmersion (ν₀ ≫ ν).left` using `by rw [Over.comp_left]; infer_instance`. Establish `: Mono (ν₀ ≫ ν)` using `Over.mono_of_mono_left _`. Establish `hA : IsAbelianScheme N₀` using `{ comm := AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν) smooth := SmoothOfRelativeDimension.smooth g N₀.hom proper := by rw [← ν₀.w]; infer_instance geomConnected := hgc }`.

Establish `hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C` using `fun x => by`. Rewrite using `[hC, ← hr]`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨x.left t, rfl⟩`. Establish `h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀)`.

Use `hno k N₀ hA n hn.two_le hnk fun x hx => ?_` and prove the remaining obligations. Establish `h2 : x ≫ ν₀ ≫ ν = 1`. Use `htor _ (by rw [← Category.assoc]; exact hmem _) ?_` and prove the remaining obligations. Rewrite using `[← MonObj.pow_comp, hx, MonObj.one_comp]`. Rewrite using `[← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]`.

Use `finite_points_of_isOpenImmersion ν₀` as an intermediate fact. Use `Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Establish `: IsReduced (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (IsReduced (Sp k))`. Take `⟨l, hl⟩` from `AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)`.

Use `⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩` and prove the remaining obligations. Rewrite using `[← ν.w, ← Category.assoc, hl, x.w]`.
-/
theorem finite_of_isClosed_abelian
    (hno : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
      ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) →
      Finite (𝟙_ (Over (Sp k)) ⟶ A)) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
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
    { comm := AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine hno k N₀ hA n hn.two_le hnk fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
    (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

/- English proof (translation)
Use `letI := zariski G`. Use `haveI := noetherianSpace_zariski G`. Establish `hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero`.

Rewrite using `[pow_zero]`. Conclude with `inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))`.

Establish `hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ^ n = z}` using `fun n => by`. Take `⟨Z', hZ', h⟩` from `exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ n) (hpow n) inferInstance inferInstance inferInstance inferInstance K Z hZ hK`. Use `isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Rewrite using `[Set.mem_preimage, ← range_left_subset_iff, ← h]`.

Simplify using `only [MonObj.comp_pow, Category.comp_id, Set.mem_setOf_eq]`. Set `F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G)` to `fun a => ⟨_, hcl (l ^ a)⟩`. Take `⟨_, ⟨a, rfl⟩, hmin⟩` from `(wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min (Set.range F) ⟨_, 0, rfl⟩`. Establish `hle : F (a + 1) ≤ F a`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `⟨y ^ l, K.pow_mem hy l, by rw [← pow_mul, ← pow_succ']⟩`. Establish `heq : F (a + 1) = F a` using `hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)`. Use `⟨a, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: x ^ (l ^ a) ∈ F (a + 1)`. Rewrite using `[heq]`.

Conclude with `⟨x, hx, rfl⟩`. Conclude with `this`.
-/
theorem exists_pow_stable {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (l : ℕ)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ^ (l ^ (a + 1)) = x ^ (l ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ^ n = z} := fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ n)
      (hpow n) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    simp only [MonObj.comp_pow, Category.comp_id, Set.mem_setOf_eq]
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl (l ^ a)⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y ^ l, K.pow_mem hy l, by rw [← pow_mul, ← pow_succ']⟩
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ^ (l ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

/- English proof (translation)
Set `e : 𝟙_ (Over (Sp k)) ⟶ G'` to `1`. Set `S : Set G'.left` to `⋃ y ∈ (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f) \ {e}, {pt y}`. Establish `hS : IsClosed S` using `(h.subset Set.diff_subset).isClosed_biUnion fun y _ => isClosed_pt y`. Establish `hsub : Set.range f.left ⊆ {pt e} ∪ S`. Use `ReducedSubgroup.range_subset_of_points f ((isClosed_pt e).union hS) fun x => ?_` and prove the remaining obligations.

Rewrite using `[range_left_subset_iff]`. Distinguish the cases in `hx : x ≫ f = e`. Conclude with `Or.inl (by rw [hx]; rfl)`. Conclude with `Or.inr (Set.mem_biUnion (x := x ≫ f) ⟨⟨x, rfl⟩, hx⟩ rfl)`. Establish `heS : pt e ∉ S`.

Introduce `he`. Take `⟨y, hy, hey⟩` from `Set.mem_iUnion₂.1 he`. Conclude with `hy.2 (pt_injective hey).symm`. Establish `hc : _root_.IsPreconnected (Set.range f.left)` using `isPreconnected_range f.left.continuous`. Establish `he : pt e ∈ Set.range f.left` using `⟨pt (1 : 𝟙_ (Over (Sp k)) ⟶ G), by`.

Rewrite using `[← pt_comp, MonObj.one_comp]⟩`. Establish `hsub' : Set.range f.left ⊆ {pt e}`. Break down `isPreconnected_iff_subset_of_disjoint_closed.1 hc _ _ (isClosed_pt e) hS hsub (by rw [Set.singleton_inter_eq_empty.2 heS, Set.inter_empty]) with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (h1 he) heS`.

Establish `: Subsingleton (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (Subsingleton (Sp k))`. Establish `: IsClosedImmersion e.left` using `isClosedImmersion_of_comp_eq_id _ _ e.w`. Take `⟨t, ht⟩` from `AbelianSubgroupFinite.exists_lift_of_range_subset f.left e.left (hsub'.trans (by rintro _ rfl; exact ⟨_, rfl⟩))`. Establish `ht' : t = G.hom`. Rewrite using `[← f.w, ← ht, Category.assoc, e.w]`.

Conclude with `(Category.comp_id _).symm`. Establish `: f = toUnit G ≫ e` using `Over.OverMorphism.ext (by rw [← ht, ht']; rfl)`. Rewrite using `[this, MonObj.comp_one]`.
-/
theorem eq_one_of_finite_range {k : Type} [Field k] [IsAlgClosed k] {G G' : Over (Sp k)} [GrpObj G]
    [GrpObj G'] [IsIntegral G.left] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom]
    (f : G ⟶ G') [IsMonHom f]
    (h : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f).Finite) : f = 1 := by
  let e : 𝟙_ (Over (Sp k)) ⟶ G' := 1
  let S : Set G'.left := ⋃ y ∈ (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f) \ {e}, {pt y}
  have hS : IsClosed S := (h.subset Set.diff_subset).isClosed_biUnion fun y _ => isClosed_pt y
  have hsub : Set.range f.left ⊆ {pt e} ∪ S := by
    refine ReducedSubgroup.range_subset_of_points f ((isClosed_pt e).union hS) fun x => ?_
    rw [range_left_subset_iff]
    by_cases hx : x ≫ f = e
    · exact Or.inl (by rw [hx]; rfl)
    · exact Or.inr (Set.mem_biUnion (x := x ≫ f) ⟨⟨x, rfl⟩, hx⟩ rfl)
  have heS : pt e ∉ S := by
    intro he
    obtain ⟨y, hy, hey⟩ := Set.mem_iUnion₂.1 he
    exact hy.2 (pt_injective hey).symm
  have hc : _root_.IsPreconnected (Set.range f.left) := isPreconnected_range f.left.continuous
  have he : pt e ∈ Set.range f.left := ⟨pt (1 : 𝟙_ (Over (Sp k)) ⟶ G), by
    rw [← pt_comp, MonObj.one_comp]⟩
  have hsub' : Set.range f.left ⊆ {pt e} := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hc _ _ (isClosed_pt e) hS hsub
      (by rw [Set.singleton_inter_eq_empty.2 heS, Set.inter_empty]) with h1 | h1
    · exact h1
    · exact absurd (h1 he) heS
  have : Subsingleton (𝟙_ (Over (Sp k))).left := inferInstanceAs (Subsingleton (Sp k))
  have : IsClosedImmersion e.left := isClosedImmersion_of_comp_eq_id _ _ e.w
  obtain ⟨t, ht⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset f.left e.left
    (hsub'.trans (by rintro _ rfl; exact ⟨_, rfl⟩))
  have ht' : t = G.hom := by
    rw [← f.w, ← ht, Category.assoc, e.w]
    exact (Category.comp_id _).symm
  have : f = toUnit G ≫ e := Over.OverMorphism.ext (by rw [← ht, ht']; rfl)
  rw [this, MonObj.comp_one]

/- English proof (translation)
Introduce `k _ _ G G' _ _ hG hG' l hl hlk f hf htor`. Use `replace htor := htor 1 (one_pow l)`. Use `hG.comm` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact.

Use `hG'.comm` as an intermediate fact. Use `hG'.smooth` as an intermediate fact. Use `hG'.quasiCompact` as an intermediate fact. Use `isIntegral_left_of_isSemiAbelian G` as an intermediate fact. Set `φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G')` to `MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y f`.

Take `⟨a, ha⟩` from `exists_pow_stable G l φ.ker (f.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G')}) ((isClosed_pt _).preimage f.left.continuous) fun x => by`. Rewrite using `[range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff, pt_injective.eq_iff]`. Both sides reduce to the same expression. Take `⟨Z', hZ', h'⟩` from `exists_isClosed_image_of_isClosed_subgroup k G G' f hf inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)`. Establish `hfin : Finite φ.range`.

Use `finite_of_isClosed_torusExtension_of_pow_eq_one (finite_of_isClosed_abelian GlobalTheory.T.finite_points_abelianVariety_of_no_torsion) k G' l inferInstance inferInstance (nonempty_torusExtension G' hG') hl hlk _ Z' hZ' (fun y => ?_) ?_` and prove the remaining obligations. Rewrite using `[← h']`. Conclude with `⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩`. Introduce and unpack `_ ⟨g, rfl⟩ hg`. Take `⟨y, hy, hyg⟩` from `ha (g ^ l) (by rw [MonoidHom.mem_ker, map_pow, hg])`.

Establish `h1 : φ (g / y) = 1` using `htor (g / y) (a + 1) (by`. Rewrite using `[div_pow, hyg, ← pow_mul, ← pow_succ', div_self'])`. Rewrite `h1` using `[map_div, MonoidHom.mem_ker.1 hy, div_one]`. Then use the resulting hypothesis. Conclude with `eq_one_of_finite_range f hfin`.
-/
theorem eq_one_of_torsion_comp_eq_one : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (l : ℕ), l.Prime → (l : k) ≠ 0 → ∀ f : G ⟶ G', IsMonHom f → (∀ (x : 𝟙_ (Over (Sp k)) ⟶ G), x ^ l = 1 → ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, ∀ a : ℕ, y ^ (l ^ a) = 1 → y ≫ f = 1) → f = 1 := by
  intro k _ _ G G' _ _ hG hG' l hl hlk f hf htor
  replace htor := htor 1 (one_pow l)
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := hG'.comm
  have := hG'.smooth
  have := hG'.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G') :=
    MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y f
  obtain ⟨a, ha⟩ := exists_pow_stable G l φ.ker (f.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G')})
    ((isClosed_pt _).preimage f.left.continuous) fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G' f hf inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one
      (finite_of_isClosed_abelian GlobalTheory.T.finite_points_abelianVariety_of_no_torsion) k G' l inferInstance inferInstance
      (nonempty_torusExtension G' hG') hl hlk _ Z' hZ' (fun y => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro _ ⟨g, rfl⟩ hg
      obtain ⟨y, hy, hyg⟩ := ha (g ^ l) (by rw [MonoidHom.mem_ker, map_pow, hg])
      have h1 : φ (g / y) = 1 := htor (g / y) (a + 1) (by
        rw [div_pow, hyg, ← pow_mul, ← pow_succ', div_self'])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range f hfin

end GlobalTheory.TorsionDense
