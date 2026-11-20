import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsionStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableClosed
open GlobalTheory.RationalPoint

/- English proof (translation)
Introduce `E _ _ k _ _ _ G _ act π hG hπ hπu C Z hZ hC hstab htor`. Use `hG.comm` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Take `⟨T⟩` from `GlobalTheory.TorsionDense.nonempty_torusExtension G hG`.

Use `letI := T.addCommGroup`. Use `letI := T.free`. Use `letI := T.finite`. Use `letI := T.grpB`. Use `haveI := T.q_hom`.

Use `haveI := T.i_hom`. Use `haveI := T.isAbelian.proper`. Use `haveI := T.isAbelian.smooth`. Use `haveI := act.hom π`. Take `⟨actB, actT, hB, hT⟩` from `GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient (𝓞 E) k G act hG T`.

Set `φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ T.B)` to `MonoidHom.mk' (fun x => x ≫ T.q) fun x y => MonObj.mul_comp x y T.q`. Set `j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X) →* (𝟙_ (Over (Sp k)) ⟶ G)` to `MonoidHom.mk' (fun x => x ≫ T.i) fun x y => MonObj.mul_comp x y T.i`. Set `m : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G)` to `MonoidHom.mk' (fun x => x ≫ act.act π) fun x y => MonObj.mul_comp x y _`. Establish `hj : Function.Injective j` using `fun x y hxy => T.isKernel.hom_ext hxy (toUnit_unique _ _)`. Establish `hker : ∀ x, φ x = 1 → ∃ t, j t = x` using `fun x hx => ⟨T.isKernel.lift x (toUnit _) hx, T.isKernel.lift_fst _ _ _⟩`.

Establish `hTf : Finite (C.comap j)`. Use `GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion E k T.X actT π hπ hπu _ (T.i.left ⁻¹' Z) (hZ.preimage T.i.left.continuous) (fun x => ?_) (fun a x hx => ?_) (fun x hx h1 => ?_)` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]`. Both sides reduce to the same expression. Rewrite `hx`, the goal using `[Subgroup.mem_comap]`.

Express the relevant statement in the definitionally equal form `(x ≫ actT.act a) ≫ T.i ∈ C`. Rewrite using `[Category.assoc, hT a, ← Category.assoc]`. Conclude with `hstab a _ hx`. Apply `hj` to reduce the goal to its premises. Rewrite using `[map_one]`.

Use `htor _ hx ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x ≫ T.i) ≫ act.act π = 1`. Rewrite using `[Category.assoc, ← hT π, ← Category.assoc, h1, MonObj.one_comp]`. Set `ψ : C →* (𝟙_ (Over (Sp k)) ⟶ T.B)` to `φ.comp C.subtype`. Establish `hK : Finite ψ.ker` using `by choose s hs using fun x : ψ.ker => hker x.1.1 x.2`.

Use `Finite.of_injective (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j)) fun x y hxy => ?_` and prove the remaining obligations. Use `congrArg (fun t : C.comap j => j t.1) hxy` as an intermediate fact. Simplify using `only [hs] at this`. Conclude with `Subtype.ext (Subtype.ext this)`. Take `⟨Z', hZ', h'⟩` from `exists_isClosed_image_of_isClosed_subgroup k G T.B T.q inferInstance inferInstance inferInstance inferInstance inferInstance C Z hZ hC`.

Establish `hR : Finite ψ.range`. Use `GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion E k T.B actB π T.isAbelian hπ hπu _ Z' hZ' (fun y => ?_) (fun a y hy => ?_) ?_` and prove the remaining obligations. Rewrite using `[← h']`. Conclude with `⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩`. Take `⟨x, rfl⟩` from `hy`.

Use `⟨⟨x.1 ≫ act.act a, hstab a _ x.2⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x.1 ≫ act.act a) ≫ T.q = (x.1 ≫ T.q) ≫ actB.act a`. Rewrite using `[Category.assoc, Category.assoc, hB]`. Introduce and unpack `_ ⟨y, rfl⟩ hy`. Establish `hmC : ∀ z : C, m z.1 ∈ C` using `fun z => hstab π _ z.2`.

Establish `hmK : ∀ z : ψ.ker, ψ ⟨m z.1.1, hmC z.1⟩ = 1` using `fun z => by`. Express the relevant statement in the definitionally equal form `(z.1.1 ≫ act.act π) ≫ T.q = 1`. Rewrite using `[Category.assoc, ← hB π, ← Category.assoc]`. Express the relevant statement in the definitionally equal form `ψ z.1 ≫ actB.act π = 1`. Rewrite using `[MonoidHom.mem_ker.1 z.2]`.

Use `haveI := actB.hom π`. Conclude with `MonObj.one_comp _`. Set `f : ψ.ker → ψ.ker` to `fun z => ⟨⟨m z.1.1, hmC z.1⟩, hmK z⟩`. Establish `hf : Function.Injective f` using `fun z₁ z₂ h => by`. Establish `h1 : m z₁.1.1 = m z₂.1.1` using `congrArg (fun z : ψ.ker => z.1.1) h`.

Establish `h2 : z₁.1.1 / z₂.1.1 = 1` using `htor _ (C.div_mem z₁.1.2 z₂.1.2) (by`. Express the relevant statement in the definitionally equal form `m (z₁.1.1 / z₂.1.1) = 1`. Rewrite using `[map_div, h1, div_self'])`. Conclude with `Subtype.ext (Subtype.ext (div_eq_one.1 h2))`. Establish `hw : ψ ⟨m y.1, hmC y⟩ = 1`.

Express the relevant statement in the definitionally equal form `(y.1 ≫ act.act π) ≫ T.q = 1`. Rewrite using `[Category.assoc, ← hB π, ← Category.assoc]`. Conclude with `hy`. Take `⟨z, hz⟩` from `(Finite.injective_iff_surjective.1 hf) ⟨⟨m y.1, hmC y⟩, hw⟩`. Establish `h1 : m z.1.1 = m y.1` using `congrArg (fun z : ψ.ker => z.1.1) hz`.

Establish `h2 : y.1 / z.1.1 = 1` using `htor _ (C.div_mem y.2 z.1.2) (by`. Express the relevant statement in the definitionally equal form `m (y.1 / z.1.1) = 1`. Rewrite using `[map_div, h1, div_self'])`. Establish `h3 : y = z.1` using `Subtype.ext (div_eq_one.1 h2)`. Rewrite using `[h3]`.

Conclude with `z.2`. Conclude with `(MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩`.
-/
theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (π : 𝓞 E), IsSemiAbelian G → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ G _ act π hG hπ hπu C Z hZ hC hstab htor
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨T⟩ := GlobalTheory.TorsionDense.nonempty_torusExtension G hG
  letI := T.addCommGroup
  letI := T.free
  letI := T.finite
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  haveI := T.isAbelian.proper
  haveI := T.isAbelian.smooth
  haveI := act.hom π
  obtain ⟨actB, actT, hB, hT⟩ := GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient (𝓞 E) k G act hG T
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ T.B) :=
    MonoidHom.mk' (fun x => x ≫ T.q) fun x y => MonObj.mul_comp x y T.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ T.i) fun x y => MonObj.mul_comp x y T.i
  let m : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ act.act π) fun x y => MonObj.mul_comp x y _
  have hj : Function.Injective j := fun x y hxy =>
    T.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨T.isKernel.lift x (toUnit _) hx, T.isKernel.lift_fst _ _ _⟩
  have hTf : Finite (C.comap j) := by
    refine GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion E k T.X actT π hπ hπu _ (T.i.left ⁻¹' Z)
      (hZ.preimage T.i.left.continuous) (fun x => ?_) (fun a x hx => ?_) (fun x hx h1 => ?_)
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · rw [Subgroup.mem_comap] at hx ⊢
      change (x ≫ actT.act a) ≫ T.i ∈ C
      rw [Category.assoc, hT a, ← Category.assoc]
      exact hstab a _ hx
    · apply hj
      rw [map_one]
      refine htor _ hx ?_
      change (x ≫ T.i) ≫ act.act π = 1
      rw [Category.assoc, ← hT π, ← Category.assoc, h1, MonObj.one_comp]
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ T.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G T.B T.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion E k T.B actB π T.isAbelian hπ hπu _ Z' hZ' (fun y => ?_) (fun a y hy => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · obtain ⟨x, rfl⟩ := hy
      refine ⟨⟨x.1 ≫ act.act a, hstab a _ x.2⟩, ?_⟩
      change (x.1 ≫ act.act a) ≫ T.q = (x.1 ≫ T.q) ≫ actB.act a
      rw [Category.assoc, Category.assoc, hB]
    · rintro _ ⟨y, rfl⟩ hy
      have hmC : ∀ z : C, m z.1 ∈ C := fun z => hstab π _ z.2
      have hmK : ∀ z : ψ.ker, ψ ⟨m z.1.1, hmC z.1⟩ = 1 := fun z => by
        change (z.1.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        change ψ z.1 ≫ actB.act π = 1
        rw [MonoidHom.mem_ker.1 z.2]
        haveI := actB.hom π
        exact MonObj.one_comp _
      let f : ψ.ker → ψ.ker := fun z => ⟨⟨m z.1.1, hmC z.1⟩, hmK z⟩
      have hf : Function.Injective f := fun z₁ z₂ h => by
        have h1 : m z₁.1.1 = m z₂.1.1 := congrArg (fun z : ψ.ker => z.1.1) h
        have h2 : z₁.1.1 / z₂.1.1 = 1 := htor _ (C.div_mem z₁.1.2 z₂.1.2) (by
          change m (z₁.1.1 / z₂.1.1) = 1
          rw [map_div, h1, div_self'])
        exact Subtype.ext (Subtype.ext (div_eq_one.1 h2))
      have hw : ψ ⟨m y.1, hmC y⟩ = 1 := by
        change (y.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        exact hy
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨⟨m y.1, hmC y⟩, hw⟩
      have h1 : m z.1.1 = m y.1 := congrArg (fun z : ψ.ker => z.1.1) hz
      have h2 : y.1 / z.1.1 = 1 := htor _ (C.div_mem y.2 z.1.2) (by
        change m (y.1 / z.1.1) = 1
        rw [map_div, h1, div_self'])
      have h3 : y = z.1 := Subtype.ext (div_eq_one.1 h2)
      rw [h3]
      exact z.2
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory.OStableClosed
