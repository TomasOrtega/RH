import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FinKer

/- English proof (translation)
Establish `hc : IsClosed (S ∩ closedPoints T)`. Rewrite using `[← Set.biUnion_of_singleton (S ∩ closedPoints T)]`. Conclude with `h.isClosed_biUnion fun x hx ↦ hx.2`. Rewrite using `[← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]`. Conclude with `h`.
-/
theorem finite_of_isClosed_of_finite_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

/- English proof (translation)
Rewrite using `[← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]`. Use `subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_` and prove the remaining obligations. Establish `: Finite (f.fiber (f y))` using `(f.fiberHomeo (f y)).finite_iff.mpr (h y hy)`. Conclude with `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)`.
-/
theorem locallyQuasiFinite_of_finite_closedFibres {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/- English proof (translation)
Take `⟨p, -, hp2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := u) (g := g) _ z h`. Establish `: JacobsonSpace ↥(pullback u g)` using `LocallyOfFiniteType.jacobsonSpace (pullback.fst u g)`. Establish `hcl : IsClosed (closure ({p} : Set ↥(pullback u g)))` using `isClosed_closure`. Establish `hne : (closure ({p} : Set ↥(pullback u g)) ∩ closedPoints _).Nonempty`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[Set.not_nonempty_iff_eq_empty]`. Use `JacobsonSpace.closure_inter_closedPoints hcl` as an intermediate fact. Rewrite `this` using `[hc, closure_empty]`. Conclude with `(this.symm ▸ subset_closure (Set.mem_singleton p) : p ∈ (∅ : Set _))`. Take `⟨q, hqp, hq₀⟩` from `hne`.

Establish `hq : IsClosed ({q} : Set ↥(pullback u g))` using `mem_closedPoints_iff.mp hq₀`. Use `⟨pointOfClosedPoint (pullback.fst u g) q hq ≫ pullback.snd u g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← pullback.condition, pointOfClosedPoint_comp_assoc]`. Express the relevant statement in the definitionally equal form `(pullback.snd u g) (pointOfClosedPoint (pullback.fst u g) q hq _) = z erw [pointOfClosedPoint_apply]`. Establish `hs : p ⤳ q` using `specializes_iff_mem_closure.mpr hqp`.

Use `(hs.map (pullback.snd u g).continuous).mem_closed hz (by rw [hp2]; rfl)` as an intermediate fact. Conclude with `this`.
-/
theorem exists_lift_of_isClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X Y : Scheme.{0}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] (u : Sp Ω ⟶ Y) (z : X) (hz : IsClosed ({z} : Set X))
    (h : u (IsLocalRing.closedPoint Ω) = g z) :
    ∃ w : Sp Ω ⟶ X, w ≫ g = u ∧ w (IsLocalRing.closedPoint Ω) = z := by
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := g) _ z h
  have : JacobsonSpace ↥(pullback u g) := LocallyOfFiniteType.jacobsonSpace (pullback.fst u g)
  have hcl : IsClosed (closure ({p} : Set ↥(pullback u g))) := isClosed_closure
  have hne : (closure ({p} : Set ↥(pullback u g)) ∩ closedPoints _).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := JacobsonSpace.closure_inter_closedPoints hcl
    rw [hc, closure_empty] at this
    exact (this.symm ▸ subset_closure (Set.mem_singleton p) : p ∈ (∅ : Set _))
  obtain ⟨q, hqp, hq₀⟩ := hne
  have hq : IsClosed ({q} : Set ↥(pullback u g)) := mem_closedPoints_iff.mp hq₀
  refine ⟨pointOfClosedPoint (pullback.fst u g) q hq ≫ pullback.snd u g, ?_, ?_⟩
  · rw [Category.assoc, ← pullback.condition, pointOfClosedPoint_comp_assoc]
  · change (pullback.snd u g) (pointOfClosedPoint (pullback.fst u g) q hq _) = z
    erw [pointOfClosedPoint_apply]
    have hs : p ⤳ q := specializes_iff_mem_closure.mpr hqp
    have := (hs.map (pullback.snd u g).continuous).mem_closed hz (by rw [hp2]; rfl)
    exact this

end GlobalTheory.AV.FinKer

namespace GlobalTheory.AV.AbVar

open GlobalTheory.AV.FinKer in

/- English proof (translation)
Introduce `K _ A B f`. Establish `: IsProper A.X.hom` using `A.ab.proper`. Establish `: IsProper B.X.hom` using `B.ab.proper`. Establish `hw : f.hom.left ≫ B.X.hom = A.X.hom` using `Over.w f.hom`. Establish `: LocallyOfFiniteType (f.hom.left ≫ B.X.hom)` using `by rw [hw]; infer_instance`.

Establish `: LocallyOfFiniteType f.hom.left` using `locallyOfFiniteType_of_comp _ B.X.hom`. Set `pt : Sp (AlgebraicClosure K)` to `IsLocalRing.closedPoint (AlgebraicClosure K)`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Set `u : Sp (AlgebraicClosure K) ⟶ B.X.left` to `(1 : B.Pt).left`.

Establish `: IsFinite (pullback.fst u f.hom.left)` using `inferInstance`. Establish `hfin` using `((pullback.fst u f.hom.left).finite_preimage_singleton pt).to_subtype`. Establish `hmem : ∀ x : (ptMap f).ker, 𝟙 _ ≫ u = x.1.left ≫ f.hom.left` using `fun x ↦ by`. Rewrite using `[Category.id_comp, ← Over.comp_left]`. Conclude with `congrArg CommaMorphism.left (MonoidHom.mem_ker.mp x.2).symm`.

Use `Finite.of_injective (β := (pullback.fst u f.hom.left) ⁻¹' {pt}) (fun x ↦ ⟨pullback.lift (𝟙 _) x.1.left (hmem x) pt, Subsingleton.elim _ _⟩) fun x y hxy ↦ ?_` and prove the remaining obligations. Establish `e` using `ext_of_apply_closedPoint_eq (pullback.fst u f.hom.left) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (congrArg Subtype.val hxy)`. Establish `e2` using `congrArg (· ≫ pullback.snd u f.hom.left) e`. Simplify using `only [pullback.lift_snd] at e2`. Conclude with `Subtype.ext (Over.OverMorphism.ext e2)`.

Introduce `hker`. Establish `: IsProper (f.hom.left ≫ B.X.hom)` using `by rw [hw]; infer_instance`. Establish `: IsProper f.hom.left` using `IsProper.of_comp _ B.X.hom`. Establish `: JacobsonSpace A.X.left` using `LocallyOfFiniteType.jacobsonSpace A.X.hom`. Establish `: LocallyQuasiFinite f.hom.left`.

Use `locallyQuasiFinite_of_finite_closedFibres f.hom.left fun y hy ↦ ?_` and prove the remaining obligations. Take `⟨a, ha, hay⟩` from `exists_lift_of_isClosed A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) y hy (Subsingleton.elim _ _)`. Set `x : A.Pt` to `Over.homMk a ha`. Establish `hcl : IsClosed (f.hom.left ⁻¹' {f.hom.left y})`. Use `f.hom.left.isClosedMap _ hy` as an intermediate fact.

Rewrite `this` using `[Set.image_singleton]`. Conclude with `this.preimage f.hom.left.continuous`. Use `finite_of_isClosed_of_finite_closedPoints hcl ?_` and prove the remaining obligations. Use `(Set.finite_range (fun k : (ptMap f).ker ↦ (x * k.1).left pt)).subset ?_` and prove the remaining obligations. Introduce and unpack `z ⟨hzS, hz⟩`.

Establish `hzS' : f.hom.left z = f.hom.left y` using `hzS`. Take `⟨w, hw1, hw2⟩` from `exists_lift_of_isClosed f.hom.left (a ≫ f.hom.left) z hz (by change f.hom.left (a pt) = _; rw [hay, hzS'])`. Set `w' : A.Pt` to `Over.homMk w (by`. Express the relevant statement in the definitionally equal form `w ≫ A.X.hom = _`. Rewrite using `[← hw, ← Category.assoc, hw1, Category.assoc, hw]`.

Conclude with `ha)`. Establish `hk : x⁻¹ * w' ∈ (ptMap f).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]`. Conclude with `Over.OverMorphism.ext hw1.symm`. Use `⟨⟨_, hk⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(x * (x⁻¹ * w')).left pt = z`. Rewrite using `[mul_inv_cancel_left]`. Conclude with `hw2`. Conclude with `IsFinite.of_isProper_of_locallyQuasiFinite _`.
-/
theorem isFinite_iff_finite_ker : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  intro K _ A B f
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : LocallyOfFiniteType (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ B.X.hom
  let pt : Sp (AlgebraicClosure K) := IsLocalRing.closedPoint (AlgebraicClosure K)
  constructor
  · intro hf
    let u : Sp (AlgebraicClosure K) ⟶ B.X.left := (1 : B.Pt).left
    have : IsFinite (pullback.fst u f.hom.left) := inferInstance
    have hfin := ((pullback.fst u f.hom.left).finite_preimage_singleton pt).to_subtype
    have hmem : ∀ x : (ptMap f).ker, 𝟙 _ ≫ u = x.1.left ≫ f.hom.left := fun x ↦ by
      rw [Category.id_comp, ← Over.comp_left]
      exact congrArg CommaMorphism.left (MonoidHom.mem_ker.mp x.2).symm
    refine Finite.of_injective (β := (pullback.fst u f.hom.left) ⁻¹' {pt})
      (fun x ↦ ⟨pullback.lift (𝟙 _) x.1.left (hmem x) pt, Subsingleton.elim _ _⟩) fun x y hxy ↦ ?_
    have e := ext_of_apply_closedPoint_eq (pullback.fst u f.hom.left) (pullback.lift_fst _ _ _)
      (pullback.lift_fst _ _ _) (congrArg Subtype.val hxy)
    have e2 := congrArg (· ≫ pullback.snd u f.hom.left) e
    simp only [pullback.lift_snd] at e2
    exact Subtype.ext (Over.OverMorphism.ext e2)
  · intro hker
    have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
    have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
    have : LocallyQuasiFinite f.hom.left := by
      refine locallyQuasiFinite_of_finite_closedFibres f.hom.left fun y hy ↦ ?_
      obtain ⟨a, ha, hay⟩ := exists_lift_of_isClosed A.X.hom (spMap (algebraMap K (AlgebraicClosure K)))
        y hy (Subsingleton.elim _ _)
      let x : A.Pt := Over.homMk a ha
      have hcl : IsClosed (f.hom.left ⁻¹' {f.hom.left y}) := by
        have := f.hom.left.isClosedMap _ hy
        rw [Set.image_singleton] at this
        exact this.preimage f.hom.left.continuous
      refine finite_of_isClosed_of_finite_closedPoints hcl ?_
      refine (Set.finite_range (fun k : (ptMap f).ker ↦ (x * k.1).left pt)).subset ?_
      rintro z ⟨hzS, hz⟩
      have hzS' : f.hom.left z = f.hom.left y := hzS
      obtain ⟨w, hw1, hw2⟩ := exists_lift_of_isClosed f.hom.left (a ≫ f.hom.left) z hz
        (by change f.hom.left (a pt) = _; rw [hay, hzS'])
      let w' : A.Pt := Over.homMk w (by
        change w ≫ A.X.hom = _
        rw [← hw, ← Category.assoc, hw1, Category.assoc, hw]; exact ha)
      have hk : x⁻¹ * w' ∈ (ptMap f).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact Over.OverMorphism.ext hw1.symm
      refine ⟨⟨_, hk⟩, ?_⟩
      change (x * (x⁻¹ * w')).left pt = z
      rw [mul_inv_cancel_left]
      exact hw2
    exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.AV.AbVar
