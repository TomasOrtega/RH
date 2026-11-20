import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace UnramifiedEndFlat

open IsLocalRing

/- English proof (translation)
Establish `hle : maximalIdeal A ≤ (maximalIdeal A).comap φ` using `Ideal.le_comap_of_map_le hm.le`. Use `flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀ fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[← hm, Ideal.map]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `⟨x, hx, by simp⟩`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, ha, hay⟩` from `hy`.

Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a + b, add_mem ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[show φ (a + b) - (y + z) = (φ a - y) + (φ b - z) by rw [map_add]; ring]`. Conclude with `add_mem hay hbz`. Consider the case `smul c y _ hy`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨d, hd⟩` from `h₀ c`. Use `⟨d * a, Ideal.mul_mem_left _ _ ha, ?_⟩` and prove the remaining obligations. Rewrite using `[show φ (d * a) - c • y = (φ d - c) * φ a + c * (φ a - y) by`. Rewrite using `[map_mul, smul_eq_mul]`.

Use the proof step `ring]`. Use `add_mem ?_ (Ideal.mul_mem_left _ _ hay)` and prove the remaining obligations. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hd (hle ha)`.
-/
theorem flat_of_map_maximalIdeal_self {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (φ : A →+* A) (hm : (maximalIdeal A).map φ = maximalIdeal A)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal A).comap φ := Ideal.le_comap_of_map_le hm.le
  refine flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀ fun y hy => ?_
  rw [← hm, Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a + b, add_mem ha hb, ?_⟩
    rw [show φ (a + b) - (y + z) = (φ a - y) + (φ b - z) by rw [map_add]; ring]
    exact add_mem hay hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨d, hd⟩ := h₀ c
    refine ⟨d * a, Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [show φ (d * a) - c • y = (φ d - c) * φ a + c * (φ a - y) by
      rw [map_mul, smul_eq_mul]; ring]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hay)
    rw [pow_two]
    exact Ideal.mul_mem_mul hd (hle ha)

/- English proof (translation)
Establish `he : (maximalIdeal B).map (e : B →+* A) = maximalIdeal A` using `map_maximalIdeal_of_surjective _ e.surjective`. Establish `h : ((e : B →+* A).comp φ).Flat`. Use `flat_of_map_maximalIdeal_self _ (by rw [← Ideal.map_map, hm, he]) fun b => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `h₀ (e.symm b)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Use `Ideal.mem_map_of_mem (e : B →+* A) ha` as an intermediate fact. Rewrite `this` using `[he]`. Simplify using `using this`. Use `h.comp (RingHom.Flat.of_bijective (f := (e.symm : A →+* B)) e.symm.bijective)` as an intermediate fact. Use `this` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] (e : B ≃+* A)
    (φ : A →+* B) (hm : (maximalIdeal A).map φ = maximalIdeal B)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal B) : φ.Flat := by
  have he : (maximalIdeal B).map (e : B →+* A) = maximalIdeal A :=
    map_maximalIdeal_of_surjective _ e.surjective
  have h : ((e : B →+* A).comp φ).Flat := by
    refine flat_of_map_maximalIdeal_self _ (by rw [← Ideal.map_map, hm, he]) fun b => ?_
    obtain ⟨a, ha⟩ := h₀ (e.symm b)
    refine ⟨a, ?_⟩
    have := Ideal.mem_map_of_mem (e : B →+* A) ha
    rw [he] at this
    simpa using this
  have := h.comp (RingHom.Flat.of_bijective (f := (e.symm : A →+* B)) e.symm.bijective)
  convert this
  ext x
  simp

/- English proof (translation)
Use `letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)`. Use `haveI := hU.isLocalization_stalk ⟨x, hx⟩`. Use `letI := g.hom.toAlgebra`. Use `letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra`. Use `haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl`.

Conclude with `Module.flat_iff_of_isLocalization (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C`.
-/
theorem flat_iff_comp_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) {C : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ C) :
    g.hom.Flat ↔ (X.presheaf.germ U x hx ≫ g).hom.Flat := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  letI := g.hom.toAlgebra
  letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.flat_iff_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hx', -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ`. Rewrite using `[flat_iff_comp_germ hU hx', TopCat.Presheaf.germ_stalkSpecializes, ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]`. Conclude with `RingHom.Flat.id _`.
-/
theorem flat_stalkSpecializes {X : Scheme.{0}} {x x' : X} (h : x ⤳ x') :
    (X.presheaf.stalkSpecializes h).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  rw [flat_iff_comp_germ hU hx', TopCat.Presheaf.germ_stalkSpecializes,
    ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]
  exact RingHom.Flat.id _

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hx', -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ`. Establish `h' : f x ⤳ f x'` using `h.map f.continuous`. Rewrite using `[flat_iff_comp_germ hU (h'.mem_open U.2 hx'), ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hx' h', Category.assoc, Scheme.Hom.stalkSpecializes_stalkMap f x x' h, ← flat_iff_comp_germ hU hx']`. Conclude with `hf.comp (flat_stalkSpecializes h)`.
-/
theorem flat_stalkMap_of_specializes {X Y : Scheme.{0}} (f : X ⟶ Y) {x x' : X} (h : x ⤳ x')
    (hf : (f.stalkMap x').hom.Flat) : (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have h' : f x ⤳ f x' := h.map f.continuous
  rw [flat_iff_comp_germ hU (h'.mem_open U.2 hx'),
    ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hx' h', Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap f x x' h, ← flat_iff_comp_germ hU hx']
  exact hf.comp (flat_stalkSpecializes h)

/- English proof (translation)
Use `Flat.of_stalkMap f fun x => ?_` and prove the remaining obligations. Take `⟨y, hy, hyc⟩` from `nonempty_inter_closedPoints (Z := closure {x}) ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed`. Conclude with `flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)`.
-/
theorem flat_of_closedPoints {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)

/- English proof (translation)
Establish `h : (residueFieldIsoBase (f ≫ g) x hx).inv = Spec.preimage (Y.fromSpecResidueField (f x) ≫ g) ≫ f.residueFieldMap x`. Apply `Spec.map_injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `h2 : Function.Surjective (residueFieldIsoBase (f ≫ g) x hx).inv` using `(ConcreteCategory.bijective_of_isIso _).2`. Rewrite `h2` using `[h]`.

Conclude with `Function.Surjective.of_comp (g := Spec.preimage (Y.fromSpecResidueField (f x) ≫ g)) h2`.
-/
theorem residueFieldMap_surjective {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ g)] (x : X)
    (hx : IsClosed {x}) : Function.Surjective (f.residueFieldMap x) := by
  have h : (residueFieldIsoBase (f ≫ g) x hx).inv =
      Spec.preimage (Y.fromSpecResidueField (f x) ≫ g) ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    simp
  have h2 : Function.Surjective (residueFieldIsoBase (f ≫ g) x hx).inv :=
    (ConcreteCategory.bijective_of_isIso _).2
  rw [h] at h2
  exact Function.Surjective.of_comp (g := Spec.preimage (Y.fromSpecResidueField (f x) ≫ g)) h2

/- English proof (translation)
Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian g`. Establish `: LocallyOfFiniteType (f ≫ g)` using `by rw [hfg]; infer_instance`. Establish `: LocallyOfFiniteType f` using `locallyOfFiniteType_of_comp f g`. Establish `h1` using `FormallyUnramified.stalkMap f x`. Establish `h2` using `LocallyOfFiniteType.stalkMap f x`.

Use `flat_of_map_maximalIdeal (X.presheaf.stalkCongr (Inseparable.of_eq hfx.symm)).commRingCatIsoToRingEquiv _ ?_ fun b => ?_` and prove the remaining obligations. Use `algebraize [(f.stalkMap x).hom]`. Establish `: IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X.presheaf.stalk x))` using `inferInstanceAs (IsLocalHom (f.stalkMap x).hom)`. Conclude with `Algebra.FormallyUnramified.map_maximalIdeal`. Take `⟨a, ha⟩` from `residueFieldMap_surjective f g x hx (X.residue x b)`.

Take `⟨a, rfl⟩` from `X.residue_surjective (f x) a`. Use `⟨a, Ideal.Quotient.eq.mp ?_⟩` and prove the remaining obligations. Conclude with `ha`.
-/
theorem flat_stalkMap_of_fixed {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (f : X ⟶ X) (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hfg : f ≫ g = g)
    [FormallyUnramified f] (x : X) (hx : IsClosed {x}) (hfx : f x = x) :
    (f.stalkMap x).hom.Flat := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (f ≫ g) := by rw [hfg]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have h1 := FormallyUnramified.stalkMap f x
  have h2 := LocallyOfFiniteType.stalkMap f x
  refine flat_of_map_maximalIdeal
    (X.presheaf.stalkCongr (Inseparable.of_eq hfx.symm)).commRingCatIsoToRingEquiv _ ?_ fun b => ?_
  · algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact Algebra.FormallyUnramified.map_maximalIdeal
  · obtain ⟨a, ha⟩ := residueFieldMap_surjective f g x hx (X.residue x b)
    obtain ⟨a, rfl⟩ := X.residue_surjective (f x) a
    refine ⟨a, Ideal.Quotient.eq.mp ?_⟩
    exact ha

end UnramifiedEndFlat

open UnramifiedEndFlat in

/- English proof (translation)
Use `LocallyOfFiniteType.jacobsonSpace G.hom` as an intermediate fact. Use `flat_of_closedPoints _ fun x hx => ?_` and prove the remaining obligations. Set `x' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2`. Set `o : G.left` to `η[G].left (IsLocalRing.closedPoint k)`. Establish `ho : IsClosed {o}` using `(pointEquivClosedPoint G.hom ⟨η[G].left, η[G].w⟩).2`.

Establish `hfo : φ.left o = o`. Establish `: η[G] ≫ φ = η[G]` using `IsMonHom.one_hom φ`. Conclude with `congr(($this).left (IsLocalRing.closedPoint k))`. Establish `h0` using `flat_stalkMap_of_fixed φ.left G.hom φ.w o ho hfo`. Set `α` to `GrpObj.mulRight (A := G) x'`.

Set `β` to `GrpObj.mulRight (A := G) (x' ≫ φ)`. Establish `hαβ : α.hom ≫ φ = φ ≫ β.hom`. Simplify using `[α, β, comp_lift_assoc]`. Establish `hα : η[G] ≫ α.hom = x'`. Simplify `lift_comp_one_left (𝟙 (𝟙_ (Over (Sp k)))) x'` using `[α, comp_lift_assoc]`.

Establish `hα' : α.hom.left o = x` using `(congr(($hα).left (IsLocalRing.closedPoint k))).trans (pointOfClosedPoint_apply G.hom x hx _)`. Establish `: IsIso α.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map α.hom))`. Establish `: IsIso β.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map β.hom))`. Establish `h1 : ((φ.left ≫ β.hom.left).stalkMap o).hom.Flat`. Rewrite using `[Scheme.Hom.stalkMap_comp]`.

Conclude with `(Flat.stalkMap β.hom.left _).comp h0`. Rewrite `h1` using `[← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp]`. Rewrite using `[← hα']`. Conclude with `(RingHom.Flat.respectsIso.cancel_right_isIso (φ.left.stalkMap (α.hom.left o)) (α.hom.left.stalkMap o)).mp h1`.
-/
theorem flat_of_formallyUnramified_grpEnd (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k))
    [GrpObj G] (φ : G ⟶ G) (hG : LocallyOfFiniteType G.hom) (hφ : IsMonHom φ)
    (hu : FormallyUnramified φ.left) : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let o : G.left := η[G].left (IsLocalRing.closedPoint k)
  have ho : IsClosed {o} := (pointEquivClosedPoint G.hom ⟨η[G].left, η[G].w⟩).2
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint k))
  have h0 := flat_stalkMap_of_fixed φ.left G.hom φ.w o ho hfo
  let α := GrpObj.mulRight (A := G) x'
  let β := GrpObj.mulRight (A := G) (x' ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp [α, β, comp_lift_assoc]
  have hα : η[G] ≫ α.hom = x' := by
    simpa [α, comp_lift_assoc] using lift_comp_one_left (𝟙 (𝟙_ (Over (Sp k)))) x'
  have hα' : α.hom.left o = x :=
    (congr(($hα).left (IsLocalRing.closedPoint k))).trans (pointOfClosedPoint_apply G.hom x hx _)
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap o).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp h0
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left o)) (α.hom.left.stalkMap o)).mp h1

end GlobalTheory
