import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

noncomputable section

namespace GlobalTheory

universe u v

/- English proof (translation)
Establish `h : (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z`. Use extensionality with `y`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Conclude with `⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩`. Introduce and unpack `⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx`. Apply `hZ'` to reduce the goal to its premises. Rewrite using `[connectedComponent_eq hyx]`. Conclude with `hZ.1.isConnected.subset_connectedComponent hy`.

Rewrite using `[← isClosed_compl_iff, h]`. Use `Set.Finite.isClosed_biUnion (NoetherianSpace.finite_irreducibleComponents.subset fun Z hZ => hZ.1) fun Z hZ => ?_` and prove the remaining obligations. Conclude with `isClosed_of_mem_irreducibleComponents Z hZ.1`.
-/
theorem isOpen_connectedComponent_of_noetherianSpace {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx
      apply hZ'
      rw [connectedComponent_eq hyx]
      exact hZ.1.isConnected.subset_connectedComponent hy
  rw [← isClosed_compl_iff, h]
  refine Set.Finite.isClosed_biUnion
    (NoetherianSpace.finite_irreducibleComponents.subset fun Z hZ => hZ.1) fun Z hZ => ?_
  exact isClosed_of_mem_irreducibleComponents Z hZ.1

/- English proof (translation)
Use `⟨fun K _ y Z p q h => ?_⟩` and prove the remaining obligations. Use `LocallyOfFiniteType.jacobsonSpace f` as an intermediate fact. Establish `hy : Surjective y` using `⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩`. Establish `hs : Surjective p` using `MorphismProperty.of_isPullback h.flip hy`. Establish `ho : UniversallyOpen p` using `MorphismProperty.of_isPullback h.flip (inferInstance : UniversallyOpen y)`.

Establish `fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b`. Introduce `x hx a b ha hb`. Set `s` to `pointOfClosedPoint f x hx`. Establish `hs : s ≫ f = 𝟙 _` using `pointOfClosedPoint_comp f x hx`. Set `t : Spec (.of K) ⟶ Z` to `h.lift (y ≫ s) (𝟙 _) (by simp [hs])`.

Establish `ht : IsPullback t y p s`. Use `IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip` and prove the remaining obligations. Rewrite using `[hs, show t ≫ q = 𝟙 _ by simp [t]]`. Conclude with `IsPullback.of_id_fst`. Take `⟨a', rfl, -⟩` from `Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k) (ha.trans (pointOfClosedPoint_apply f x hx _).symm)`.

Take `⟨b', rfl, -⟩` from `Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k) (hb.trans (pointOfClosedPoint_apply f x hx _).symm)`. Rewrite using `[Subsingleton.elim a' b']`. Establish `hne : Nonempty Z` using `(p.surjective (Classical.arbitrary X)).nonempty`. Establish `: PreconnectedSpace Z`. Use `preconnectedSpace_iff_clopen.2 fun U hU => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h₁ : (p '' U).Nonempty` using `hc.1.image _`. Establish `h₂ : (p '' Uᶜ).Nonempty` using `(Set.nonempty_compl.2 hc.2).image _`. Establish `o₁ : IsOpen (p '' U)` using `p.isOpenMap _ hU.isOpen`.

Establish `o₂ : IsOpen (p '' Uᶜ)` using `p.isOpenMap _ hU.compl.isOpen`. Establish `hcov : p '' U ∪ p '' Uᶜ = Set.univ`. Rewrite using `[← Set.image_union, Set.union_compl_self, Set.image_univ, p.surjective.range_eq]`. Take `⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hx⟩` from `nonempty_inter_closedPoints (nonempty_inter o₁ o₂ hcov h₁ h₂) (o₁.inter o₂).isLocallyClosed`. Conclude with `hb (fib x hx a b hax hbx ▸ ha)`.

Conclude with `⟨hne⟩`.
-/
theorem geometricallyConnected_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)

  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    let s := pointOfClosedPoint f x hx
    have hs : s ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
    let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
    have ht : IsPullback t y p s := by
      refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
      rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
      exact IsPullback.of_id_fst
    obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k)
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
    obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
    rw [Subsingleton.elim a' b']
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    by_contra hc
    push Not at hc
    have h₁ : (p '' U).Nonempty := hc.1.image _
    have h₂ : (p '' Uᶜ).Nonempty := (Set.nonempty_compl.2 hc.2).image _
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU.isOpen
    have o₂ : IsOpen (p '' Uᶜ) := p.isOpenMap _ hU.compl.isOpen
    have hcov : p '' U ∪ p '' Uᶜ = Set.univ := by
      rw [← Set.image_union, Set.union_compl_self, Set.image_univ, p.surjective.range_eq]
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hx⟩ := nonempty_inter_closedPoints
      (nonempty_inter o₁ o₂ hcov h₁ h₂) (o₁.inter o₂).isLocallyClosed
    exact hb (fib x hx a b hax hbx ▸ ha)
  exact ⟨hne⟩

section Sub

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A N : C} [GrpObj N]

/- English proof (translation)
Establish `he' : ∀ {T : C} (t : T ⟶ 𝟙_ C), t ≫ e ≫ n = 1` using `fun t => by`. Rewrite using `[he, Hom.one_def, toUnit_unique t (toUnit _)]`. Establish `hm' : ∀ {T : C} (t : T ⟶ A ⊗ A), t ≫ m ≫ n = (t ≫ fst _ _ ≫ n) * (t ≫ snd _ _ ≫ n)` using `fun t => by`. Rewrite using `[hm, Hom.mul_def, ← Category.assoc]`. Use `congr 1`.

Apply the tactic sequence `ext <;> simp`. Establish `hm'' : m ≫ n = (fst _ _ ≫ n) * (snd _ _ ≫ n)` using `by simpa using hm' (𝟙 _)`. Establish `hi' : i ≫ n = n⁻¹` using `by rw [hi, Hom.inv_def]`. Use `letI : GrpObj A := { one := e mul := m inv := i one_mul := by`. Rewrite using `[← cancel_mono n, Category.assoc, hm', whiskerRight_fst_assoc, whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]`.

Use `mul_one := by`. Rewrite using `[← cancel_mono n, Category.assoc, hm', whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]`. Use `mul_assoc := by`. Rewrite using `[← cancel_mono n, Category.assoc, hm', Category.assoc, Category.assoc, hm' (A ◁ m), whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm', hm', MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc]`. Simplify using the standard rewrite rules.

Use `left_inv := by`. Rewrite using `[← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc, lift_snd_assoc, hi', Category.id_comp, inv_mul_cancel]`. Use `right_inv := by`. Rewrite using `[← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc, lift_snd_assoc, hi', Category.id_comp, mul_inv_cancel] }`. Conclude with `⟨this, ⟨he, hm⟩⟩`.
-/
theorem exists_grpObj_of_mono_of_fac (n : A ⟶ N) [Mono n] (e : 𝟙_ C ⟶ A) (m : A ⊗ A ⟶ A) (i : A ⟶ A)
    (he : e ≫ n = η[N]) (hm : m ≫ n = (n ⊗ₘ n) ≫ μ[N]) (hi : i ≫ n = n ≫ ι[N]) :
    ∃ _ : GrpObj A, IsMonHom n := by
  have he' : ∀ {T : C} (t : T ⟶ 𝟙_ C), t ≫ e ≫ n = 1 := fun t => by
    rw [he, Hom.one_def, toUnit_unique t (toUnit _)]
  have hm' : ∀ {T : C} (t : T ⟶ A ⊗ A), t ≫ m ≫ n = (t ≫ fst _ _ ≫ n) * (t ≫ snd _ _ ≫ n) :=
    fun t => by
      rw [hm, Hom.mul_def, ← Category.assoc]
      congr 1
      ext <;> simp
  have hm'' : m ≫ n = (fst _ _ ≫ n) * (snd _ _ ≫ n) := by simpa using hm' (𝟙 _)
  have hi' : i ≫ n = n⁻¹ := by rw [hi, Hom.inv_def]
  letI : GrpObj A :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
          he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono n, Category.assoc, hm', Category.assoc, Category.assoc,
          hm' (A ◁ m), whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, hm', hm', MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc]
        simp
      left_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, inv_mul_cancel]
      right_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, mul_inv_cancel] }
  exact ⟨this, ⟨he, hm⟩⟩

end Sub

/- English proof (translation)
Set `pt : Sp k` to `IsLocalRing.closedPoint k`. Set `F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left` to `fun x => x.left pt`. Establish `hF : Function.Injective F` using `fun x y hxy => Over.OverMorphism.ext (ext_of_apply_closedPoint_eq N.hom x.w y.w hxy)`. Establish `ho : ∀ x, IsOpen {F x}` using `fun x => by`. Establish `hx : η[N] ≫ (GrpObj.mulRight x).hom = x`.

Simplify `lift_comp_one_left (𝟙 _) x` using `[comp_lift_assoc]`. Establish `: IsIso (GrpObj.mulRight x).hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))`. Establish `h₁ : IsOpenMap x.left`. Rewrite using `[← hx, Over.comp_left]`. Conclude with `(GrpObj.mulRight x).hom.left.isOpenMap.comp h`.

Establish `h₂` using `h₁ {pt} (by`. Establish `: Subsingleton (Sp k)` using `inferInstance`. Use `isOpen_univ` and compare the differences between its conclusion and the goal. Conclude with `Set.eq_univ_of_forall fun a => this.elim _ _)`. Rewrite `h₂` using `[Set.image_singleton]`. Then use the resulting hypothesis.

Take `⟨t, -, ht⟩` from `(NoetherianSpace.isCompact (Set.range F)).elim_nhds_subcover (fun y => {y}) (by rintro _ ⟨x, rfl⟩; exact (ho x).mem_nhds rfl)`. Establish `: (Set.range F).Finite` using `t.finite_toSet.subset fun y hy => by simpa using ht hy`. Conclude with `(Set.finite_range_iff hF).1 this`.
-/
theorem finite_points_of_isOpenMap_unit {k : Type} [Field k] [IsAlgClosed k] (N : Over (Sp k))
    [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    (h : IsOpenMap η[N].left) : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  have hF : Function.Injective F := fun x y hxy =>
    Over.OverMorphism.ext (ext_of_apply_closedPoint_eq N.hom x.w y.w hxy)
  have ho : ∀ x, IsOpen {F x} := fun x => by
    have hx : η[N] ≫ (GrpObj.mulRight x).hom = x := by
      simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    have h₁ : IsOpenMap x.left := by
      rw [← hx, Over.comp_left]
      exact (GrpObj.mulRight x).hom.left.isOpenMap.comp h
    have h₂ := h₁ {pt} (by
      have : Subsingleton (Sp k) := inferInstance
      convert isOpen_univ
      exact Set.eq_univ_of_forall fun a => this.elim _ _)
    rwa [Set.image_singleton] at h₂
  obtain ⟨t, -, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_nhds_subcover
    (fun y => {y}) (by rintro _ ⟨x, rfl⟩; exact (ho x).mem_nhds rfl)
  have : (Set.range F).Finite := t.finite_toSet.subset fun y hy => by simpa using ht hy
  exact (Set.finite_range_iff hF).1 this

/- English proof (translation)
Introduce `k _ _ N _ hs hq`. Establish `: IsLocallyNoetherian N.left` using `LocallyOfFiniteType.isLocallyNoetherian N.hom`. Establish `: CompactSpace N.left` using `QuasiCompact.compactSpace_of_compactSpace N.hom`. Establish `: IsNoetherian N.left` using `{}`. Set `pt : (𝟙_ (Over (Sp k))).left` to `IsLocalRing.closedPoint k`.

Set `e₀ : N.left` to `η[N].left pt`. Set `U : N.left.Opens` to `⟨connectedComponent e₀, isOpen_connectedComponent_of_noetherianSpace e₀⟩`. Set `N₀ : Over (Sp k)` to `Over.mk (U.ι ≫ N.hom)`. Set `ν : N₀ ⟶ N` to `Over.homMk U.ι rfl`. Establish `hνo : IsOpenImmersion ν.left` using `inferInstanceAs (IsOpenImmersion U.ι)`.

Establish `hr : Set.range ν.left = connectedComponent e₀` using `U.range_ι`. Establish `hνc : IsClosedImmersion ν.left` using `.of_isPreimmersion _ (hr ▸ isClosed_connectedComponent)`. Establish `: Mono ν` using `Over.mono_of_mono_left ν`. Establish `hsm : Smooth N₀.hom` using `inferInstanceAs (Smooth (U.ι ≫ N.hom))`. Establish `hc : ConnectedSpace N₀.left` using `isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := e₀))`.

Establish `hg : GeometricallyConnected N₀.hom` using `geometricallyConnected_of_isAlgClosed N₀.hom`. Establish `fac : ∀ (T : Over (Sp k)) [ConnectedSpace T.left] (φ : T ⟶ N) (t : 𝟙_ _ ⟶ T), t ≫ φ = η[N] → ∃ ψ : T ⟶ N₀, ψ ≫ ν = φ`. Introduce `T _ φ t ht`. Establish `hsub : Set.range φ.left ⊆ Set.range ν.left`. Rewrite using `[hr]`.

Use `(isConnected_range φ.left.continuous).subset_connectedComponent ⟨t.left pt, ?_⟩` and prove the remaining obligations. Simplify using `only [e₀, ← ht, Over.comp_left, Scheme.Hom.comp_apply]`. Use `⟨Over.homMk (IsOpenImmersion.lift ν.left φ.left hsub) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← ν.w, IsOpenImmersion.lift_fac_assoc, φ.w]`. Conclude with `Over.OverMorphism.ext (IsOpenImmersion.lift_fac ν.left φ.left hsub)`.

Establish `: ConnectedSpace (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (ConnectedSpace (Sp k))`. Take `⟨e, he⟩` from `fac (𝟙_ _) η[N] (𝟙 _) (Category.id_comp _)`. Establish `: ConnectedSpace (N₀ ⊗ N₀).left` using `inferInstanceAs (ConnectedSpace ↥(pullback N₀.hom N₀.hom))`. Take `⟨m, hm⟩` from `fac (N₀ ⊗ N₀) ((ν ⊗ₘ ν) ≫ μ[N]) (lift e e) (by simpa [he] using lift_comp_one_left (𝟙 _) η[N])`. Take `⟨i, hi⟩` from `fac N₀ (ν ≫ ι[N]) e (by simp [reassoc_of% he])`.

Take `⟨G, hG⟩` from `exists_grpObj_of_mono_of_fac ν e m i he hm hi`. Take `⟨g, hgd⟩` from `exists_dim_of_preconnected N₀.hom (e.left pt)`. Use `⟨N₀, G, ν, g, hG, hνo, hνc, hg, hgd, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `: Etale N₀.hom` using `(Etale.iff_smoothOfRelativeDimension_zero _).2 hgd`.

Establish `: Etale (e.left ≫ N₀.hom)`. Rewrite using `[e.w]`. Conclude with `inferInstanceAs (Etale (𝟙 (Sp k)))`. Establish `: Etale e.left` using `Etale.of_comp e.left N₀.hom`. Use `finite_points_of_isOpenMap_unit N ?_` and prove the remaining obligations.

Rewrite using `[← he, Over.comp_left]`. Conclude with `(e.left ≫ ν.left).isOpenMap`.
-/
theorem exists_neutralComponent : ∀ (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N], Smooth N.hom → QuasiCompact N.hom → ∃ (N₀ : Over (Sp k)) (_ : GrpObj N₀) (ν : N₀ ⟶ N) (g : ℕ), IsMonHom ν ∧ IsOpenImmersion ν.left ∧ IsClosedImmersion ν.left ∧ GeometricallyConnected N₀.hom ∧ SmoothOfRelativeDimension g N₀.hom ∧ (g = 0 → Finite (𝟙_ (Over (Sp k)) ⟶ N)) := by
  intro k _ _ N _ hs hq
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let e₀ : N.left := η[N].left pt
  let U : N.left.Opens := ⟨connectedComponent e₀, isOpen_connectedComponent_of_noetherianSpace e₀⟩
  let N₀ : Over (Sp k) := Over.mk (U.ι ≫ N.hom)
  let ν : N₀ ⟶ N := Over.homMk U.ι rfl
  have hνo : IsOpenImmersion ν.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range ν.left = connectedComponent e₀ := U.range_ι
  have hνc : IsClosedImmersion ν.left := .of_isPreimmersion _ (hr ▸ isClosed_connectedComponent)
  have : Mono ν := Over.mono_of_mono_left ν
  have hsm : Smooth N₀.hom := inferInstanceAs (Smooth (U.ι ≫ N.hom))
  have hc : ConnectedSpace N₀.left :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := e₀))
  have hg : GeometricallyConnected N₀.hom := geometricallyConnected_of_isAlgClosed N₀.hom

  have fac : ∀ (T : Over (Sp k)) [ConnectedSpace T.left] (φ : T ⟶ N) (t : 𝟙_ _ ⟶ T),
      t ≫ φ = η[N] → ∃ ψ : T ⟶ N₀, ψ ≫ ν = φ := by
    intro T _ φ t ht
    have hsub : Set.range φ.left ⊆ Set.range ν.left := by
      rw [hr]
      refine (isConnected_range φ.left.continuous).subset_connectedComponent ⟨t.left pt, ?_⟩
      simp only [e₀, ← ht, Over.comp_left, Scheme.Hom.comp_apply]
    refine ⟨Over.homMk (IsOpenImmersion.lift ν.left φ.left hsub) ?_, ?_⟩
    · rw [← ν.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac ν.left φ.left hsub)
  have : ConnectedSpace (𝟙_ (Over (Sp k))).left := inferInstanceAs (ConnectedSpace (Sp k))
  obtain ⟨e, he⟩ := fac (𝟙_ _) η[N] (𝟙 _) (Category.id_comp _)
  have : ConnectedSpace (N₀ ⊗ N₀).left :=
    inferInstanceAs (ConnectedSpace ↥(pullback N₀.hom N₀.hom))
  obtain ⟨m, hm⟩ := fac (N₀ ⊗ N₀) ((ν ⊗ₘ ν) ≫ μ[N]) (lift e e)
    (by simpa [he] using lift_comp_one_left (𝟙 _) η[N])
  obtain ⟨i, hi⟩ := fac N₀ (ν ≫ ι[N]) e (by simp [reassoc_of% he])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono_of_fac ν e m i he hm hi
  obtain ⟨g, hgd⟩ := exists_dim_of_preconnected N₀.hom (e.left pt)
  refine ⟨N₀, G, ν, g, hG, hνo, hνc, hg, hgd, ?_⟩
  rintro rfl
  have : Etale N₀.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hgd
  have : Etale (e.left ≫ N₀.hom) := by
    rw [e.w]; exact inferInstanceAs (Etale (𝟙 (Sp k)))
  have : Etale e.left := Etale.of_comp e.left N₀.hom
  refine finite_points_of_isOpenMap_unit N ?_
  rw [← he, Over.comp_left]
  exact (e.left ≫ ν.left).isOpenMap

end GlobalTheory
