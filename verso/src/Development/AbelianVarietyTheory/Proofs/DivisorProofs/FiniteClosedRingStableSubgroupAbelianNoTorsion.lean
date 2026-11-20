import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsionStatement

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableAbelian

/- English proof (translation)
Introduce `k _ O _ B N _ _ act ν hν hνc hred h`. Establish `: Mono ν` using `Over.mono_of_mono_left _`. Establish `hl : ∀ a : O, ∃ l : N ⟶ N, l ≫ ν = ν ≫ act.act a` using `fun a => by`. Take `⟨l, hl⟩` from `GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (ν ≫ act.act a).left ν.left (h a)`. Use `⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩` and prove the remaining obligations.

Rewrite using `[← ν.w, ← Category.assoc, hl, Over.comp_left, Category.assoc, (act.act a).w, ν.w]`. Use `choose l hl using hl`. Establish `hm : ∀ a, IsMonHom (l a)` using `fun a => by`. Use `act.hom a` as an intermediate fact. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← cancel_mono ν, Category.assoc, hl, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]`. Rewrite using `[← cancel_mono ν, Category.assoc, hl, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hl]`. Use `⟨⟨l, hm, ?_, ?_, ?_⟩, hl⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono ν, hl, act.one, Category.id_comp, Category.comp_id]`. Introduce `a b`.

Rewrite using `[← cancel_mono ν, hl, act.mul, Category.assoc, hl, reassoc_of% (hl a)]`. Introduce `a b`. Rewrite using `[← cancel_mono ν, hl, act.add, MonObj.comp_mul, MonObj.mul_comp, hl, hl]`.
-/
theorem restrict : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (B N : Over (Sp k)) [GrpObj B] [GrpObj N] (act : OAct O B) (ν : N ⟶ B), IsMonHom ν → IsClosedImmersion ν.left → IsReduced N.left → (∀ a : O, Set.range (ν ≫ act.act a).left ⊆ Set.range ν.left) → ∃ act' : OAct O N, ∀ a, act'.act a ≫ ν = ν ≫ act.act a := by
  intro k _ O _ B N _ _ act ν hν hνc hred h
  have : Mono ν := Over.mono_of_mono_left _
  have hl : ∀ a : O, ∃ l : N ⟶ N, l ≫ ν = ν ≫ act.act a := fun a => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (ν ≫ act.act a).left ν.left (h a)
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, Over.comp_left, Category.assoc, (act.act a).w, ν.w]
  choose l hl using hl
  have hm : ∀ a, IsMonHom (l a) := fun a => by
    have := act.hom a
    constructor
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hl]
  refine ⟨⟨l, hm, ?_, ?_, ?_⟩, hl⟩
  · rw [← cancel_mono ν, hl, act.one, Category.id_comp, Category.comp_id]
  · intro a b
    rw [← cancel_mono ν, hl, act.mul, Category.assoc, hl, reassoc_of% (hl a)]
  · intro a b
    rw [← cancel_mono ν, hl, act.add, MonObj.comp_mul, MonObj.mul_comp, hl, hl]

/- English proof (translation)
Introduce `k _ N₀ N _ _ ν₀ f hν₀ hf ho hc hconn`. Use `haveI := ho`. Use `haveI := hc`. Establish `hcl : IsClopen (Set.range ν₀.left)` using `⟨ν₀.left.isClosedEmbedding.isClosed_range, ν₀.left.isOpenEmbedding.isOpen_range⟩`. Establish `hpre : _root_.IsPreconnected (Set.range (ν₀ ≫ f).left)` using `isPreconnected_range (ν₀ ≫ f).left.continuous`.

Set `t : (𝟙_ (Over (Sp k))).left` to `IsLocalRing.closedPoint k`. Establish `e2 : η[N₀] ≫ ν₀ ≫ f = η[N₀] ≫ ν₀`. Rewrite using `[IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]`. Establish `he : (η[N₀] ≫ ν₀ ≫ f).left t ∈ Set.range (ν₀ ≫ f).left ∩ Set.range ν₀.left`. Use `⟨⟨η[N₀].left t, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[e2]`. Conclude with `⟨η[N₀].left t, rfl⟩`. Conclude with `hpre.subset_isClopen hcl ⟨_, he⟩`.
-/
theorem range_comp_subset : ∀ (k : Type) [Field k] (N₀ N : Over (Sp k)) [GrpObj N₀] [GrpObj N] (ν₀ : N₀ ⟶ N) (f : N ⟶ N), IsMonHom ν₀ → IsMonHom f → IsOpenImmersion ν₀.left → IsClosedImmersion ν₀.left → ConnectedSpace N₀.left → Set.range (ν₀ ≫ f).left ⊆ Set.range ν₀.left := by
  intro k _ N₀ N _ _ ν₀ f hν₀ hf ho hc hconn
  haveI := ho
  haveI := hc
  have hcl : IsClopen (Set.range ν₀.left) :=
    ⟨ν₀.left.isClosedEmbedding.isClosed_range, ν₀.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (Set.range (ν₀ ≫ f).left) :=
    isPreconnected_range (ν₀ ≫ f).left.continuous
  let t : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have e2 : η[N₀] ≫ ν₀ ≫ f = η[N₀] ≫ ν₀ := by
    rw [IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have he : (η[N₀] ≫ ν₀ ≫ f).left t ∈ Set.range (ν₀ ≫ f).left ∩ Set.range ν₀.left := by
    refine ⟨⟨η[N₀].left t, rfl⟩, ?_⟩
    rw [e2]
    exact ⟨η[N₀].left t, rfl⟩
  exact hpre.subset_isClopen hcl ⟨_, he⟩

/- English proof (translation)
Introduce `E _ _ k _ _ _ B _ act π hB hπ0 hπu C Z hZ hC hstab htor`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.comm` as an intermediate fact. Take `⟨N, _, ν, hν, hνc, hNs, hr⟩` from `GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC`.

Establish `hNp : IsProper N.hom` using `by rw [← ν.w]; infer_instance`. Take `⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩` from `GlobalTheory.exists_neutralComponent k N hNs inferInstance`. Establish `: IsClosedImmersion (ν₀ ≫ ν).left` using `by rw [Over.comp_left]; infer_instance`. Establish `: Mono (ν₀ ≫ ν)` using `Over.mono_of_mono_left _`. Establish `: Mono ν` using `Over.mono_of_mono_left _`.

Establish `hA : IsAbelianScheme N₀` using `{ comm := GlobalTheory.AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν) smooth := SmoothOfRelativeDimension.smooth g N₀.hom proper := by rw [← ν₀.w]; infer_instance geomConnected := hgc }`. Establish `hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C` using `fun x => by`. Rewrite using `[hC, ← hr]`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨x.left t, rfl⟩`.

Establish `: IsReduced (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (IsReduced (Sp k))`. Establish `hlift : ∀ x ∈ C, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x` using `fun x hx => by`. Take `⟨l, hl⟩` from `GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)`. Conclude with `⟨Over.homMk l (by rw [← ν.w, ← Category.assoc, hl, x.w]), Over.OverMorphism.ext hl⟩`. Establish `hNred : IsReduced N.left` using `isReduced_of_smooth N.hom`.

Take `⟨actN, hactN⟩` from `restrict k (𝓞 E) B N act ν hν hνc hNred fun a => by`. Rewrite using `[hr]`. Use `GlobalTheory.ReducedSubgroup.range_subset_of_points (ν ≫ act.act a) hZ fun x => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← hC]`. Conclude with `hstab a _ (hmem x)`.

Establish `: Smooth N₀.hom` using `SmoothOfRelativeDimension.smooth g N₀.hom`. Establish `hN₀red : IsReduced N₀.left` using `isReduced_of_smooth N₀.hom`. Establish `hconn : ConnectedSpace N₀.left` using `GeometricallyConnected.connectedSpace_of_subsingleton N₀.hom`. Take `⟨act₀, hact₀⟩` from `restrict k (𝓞 E) N N₀ actN ν₀ hν₀ hν₀c hN₀red fun a => range_comp_subset k N₀ N ν₀ (actN.act a) hν₀ (actN.hom a) hν₀o hν₀c hconn`. Establish `h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀)`.

Use `GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion E k N₀ act₀ π g hA hg hπ0 hπu fun x hx => ?_` and prove the remaining obligations. Establish `h2 : x ≫ ν₀ ≫ ν = 1`. Use `htor _ (by rw [← Category.assoc]; exact hmem _) ?_` and prove the remaining obligations. Establish `e : (x ≫ ν₀ ≫ ν) ≫ act.act π = (x ≫ act₀.act π) ≫ ν₀ ≫ ν`. Simplify using `only [Category.assoc, ← hactN, reassoc_of% (hact₀ π)]`.

Rewrite using `[e, hx, MonObj.one_comp]`. Rewrite using `[← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]`. Use `GlobalTheory.TorsionDense.finite_points_of_isOpenImmersion ν₀` as an intermediate fact. Use `Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`.

Take `⟨y, hy⟩` from `hlift x hx`. Conclude with `⟨y, Subtype.ext hy⟩`.
-/
theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ B _ act π hB hπ0 hπu C Z hZ hC hstab htor
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
  have : Mono ν := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := GlobalTheory.AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have hlift : ∀ x ∈ C, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x := fun x hx => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
      (hr ▸ (hC x).1 hx)
    exact ⟨Over.homMk l (by rw [← ν.w, ← Category.assoc, hl, x.w]), Over.OverMorphism.ext hl⟩
  have hNred : IsReduced N.left := isReduced_of_smooth N.hom
  obtain ⟨actN, hactN⟩ := restrict k (𝓞 E) B N act ν hν hνc hNred fun a => by
    rw [hr]
    refine GlobalTheory.ReducedSubgroup.range_subset_of_points (ν ≫ act.act a) hZ fun x => ?_
    rw [← Category.assoc, ← hC]
    exact hstab a _ (hmem x)
  have : Smooth N₀.hom := SmoothOfRelativeDimension.smooth g N₀.hom
  have hN₀red : IsReduced N₀.left := isReduced_of_smooth N₀.hom
  have hconn : ConnectedSpace N₀.left := GeometricallyConnected.connectedSpace_of_subsingleton N₀.hom
  obtain ⟨act₀, hact₀⟩ := restrict k (𝓞 E) N N₀ actN ν₀ hν₀ hν₀c hN₀red fun a =>
    range_comp_subset k N₀ N ν₀ (actN.act a) hν₀ (actN.hom a) hν₀o hν₀c hconn
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion E k N₀ act₀ π g hA hg hπ0 hπu fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      have e : (x ≫ ν₀ ≫ ν) ≫ act.act π = (x ≫ act₀.act π) ≫ ν₀ ≫ ν := by
        simp only [Category.assoc, ← hactN, reassoc_of% (hact₀ π)]
      rw [e, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := GlobalTheory.TorsionDense.finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hlift x hx
  exact ⟨y, Subtype.ext hy⟩

end GlobalTheory.OStableAbelian
