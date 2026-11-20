import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteEndFlat

/- English proof (translation)
Introduce `x y hxy`. Establish `h : y ⤳ x` using `hxy.le`. Use `lt_of_le_not_ge (show f y ⤳ f x from h.map f.continuous) fun h' => hxy.not_ge ?_` and prove the remaining obligations. Establish `e : f y = f x` using `((h.map f.continuous).antisymm h').eq`. Establish `hd` using `(f.isDiscrete_preimage_singleton (f x)).to_subtype`.

Establish `h2 : (⟨y, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩` using `(subtype_specializes_iff _ _).mpr h`. Establish `: y = x` using `congrArg Subtype.val h2.eq`. Conclude with `this.le`.
-/
theorem strictMono_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    StrictMono (f : X → Y) := by
  intro x y hxy
  have h : y ⤳ x := hxy.le
  refine lt_of_le_not_ge (show f y ⤳ f x from h.map f.continuous) fun h' => hxy.not_ge ?_
  have e : f y = f x := ((h.map f.continuous).antisymm h').eq
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨y, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr h
  have : y = x := congrArg Subtype.val h2.eq
  exact this.le

/- English proof (translation)
Establish `hs` using `strictMono_of_locallyQuasiFinite f`. Set `g : Set.Ici o → Set.Ici o` to `fun x => ⟨f x, ho.ge.trans (show f x ⤳ f o from Specializes.map (show x.1 ⤳ o from x.2) f.continuous)⟩`. Establish `hg : StrictMono g` using `fun x y h => hs h`. Set `ξ : Set.Ici o` to `⟨genericPoint X, genericPoint_specializes o⟩`. Establish `hfin : Order.height (g ξ) < ⊤`.

Establish `h1` using `Order.height_le_krullDim (g ξ)`. Rewrite `h1` using `[← Order.coheight_eq_krullDim_Ici, ← ringKrullDim_stalk_eq_coheight]`. Establish `h2` using `h1.trans_lt ringKrullDim_lt_top`. Conclude with `WithBot.coe_lt_coe.mp h2`. Establish `hle : g ξ ≤ ξ` using `genericPoint_specializes (f (genericPoint X))`.

Establish `hge : ξ ≤ g ξ`. Assume the negation of the conclusion as `h`. Conclude with `(Order.height_strictMono (lt_of_le_not_ge hle h) hfin).not_ge (Order.height_le_height_apply_of_strictMono g hg ξ)`. Conclude with `(Specializes.antisymm (show f (genericPoint X) ⤳ genericPoint X from hge) (genericPoint_specializes _)).eq`.
-/
theorem apply_genericPoint {X : Scheme.{0}} [IrreducibleSpace X] [IsLocallyNoetherian X]
    (f : X ⟶ X) [LocallyQuasiFinite f] {o : X} (ho : f o = o) :
    f (genericPoint X) = genericPoint X := by
  have hs := strictMono_of_locallyQuasiFinite f
  let g : Set.Ici o → Set.Ici o := fun x =>
    ⟨f x, ho.ge.trans (show f x ⤳ f o from Specializes.map (show x.1 ⤳ o from x.2) f.continuous)⟩
  have hg : StrictMono g := fun x y h => hs h
  let ξ : Set.Ici o := ⟨genericPoint X, genericPoint_specializes o⟩
  have hfin : Order.height (g ξ) < ⊤ := by
    have h1 := Order.height_le_krullDim (g ξ)
    rw [← Order.coheight_eq_krullDim_Ici, ← ringKrullDim_stalk_eq_coheight] at h1
    have h2 := h1.trans_lt ringKrullDim_lt_top
    exact WithBot.coe_lt_coe.mp h2
  have hle : g ξ ≤ ξ := genericPoint_specializes (f (genericPoint X))
  have hge : ξ ≤ g ξ := by
    by_contra h
    exact (Order.height_strictMono (lt_of_le_not_ge hle h) hfin).not_ge
      (Order.height_le_height_apply_of_strictMono g hg ξ)
  exact (Specializes.antisymm (show f (genericPoint X) ⤳ genericPoint X from hge)
    (genericPoint_specializes _)).eq

/- English proof (translation)
Use `algebraize [φ]`. Establish `: Module.FinitePresentation A B` using `Module.finitePresentation_of_finite A B`. Take `⟨r, hr, hfree, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)`. Use `⟨r, nonZeroDivisors.ne_zero hr, fun C _ _ _ => ?_⟩` and prove the remaining obligations. Use `letI : Algebra A C := ((algebraMap B C).comp φ).toAlgebra`.

Use `haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) C := by`. Rewrite using `[Algebra.algebraMapSubmonoid_powers]`. Use the matching hypothesis. Establish `h1 : Module.Flat A (LocalizedModule (Submonoid.powers r) B)` using `Module.Flat.trans A (Localization (Submonoid.powers r)) _`.

Conclude with `Module.Flat.of_linearEquiv (IsLocalizedModule.iso (Submonoid.powers r) (IsScalarTower.toAlgHom A B C).toLinearMap).symm`.
-/
theorem exists_flat_away {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A]
    (φ : A →+* B) (hφ : φ.Finite) :
    ∃ r : A, r ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra B C] [IsLocalization.Away (φ r) C],
      ((algebraMap B C).comp φ).Flat := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun C _ _ _ => ?_⟩
  letI : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) C := by
    rw [Algebra.algebraMapSubmonoid_powers]; assumption
  have h1 : Module.Flat A (LocalizedModule (Submonoid.powers r) B) :=
    Module.Flat.trans A (Localization (Submonoid.powers r)) _
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers r) (IsScalarTower.toAlgHom A B C).toLinearMap).symm

open UnramifiedEndFlat in

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hξ, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ`. Establish `: Nonempty U` using `⟨⟨_, hξ⟩⟩`. Establish `: IsNoetherianRing Γ(Y, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Take `⟨r, hr, H⟩` from `exists_flat_away (f.app U).hom (f.finite_app U hU)`. Establish `hV : IsAffineOpen (f ⁻¹ᵁ U)` using `hU.preimage f`.

Use `⟨X.basicOpen (f.app U r), ⟨genericPoint X, ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.preimage_basicOpen, SetLike.mem_coe, Scheme.Hom.mem_preimage, hf]`. Use `((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen r).2).mpr ?_` and prove the remaining obligations. Rewrite using `[Set.univ_inter]`. Conclude with `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp (by simpa using hr)`.

Use `hV.isLocalization_basicOpen (f.app U r)` as an intermediate fact. Establish `h1` using `H Γ(X, X.basicOpen (f.app U r))`. Establish `hxU : x ∈ f ⁻¹ᵁ U` using `X.basicOpen_le _ hx`. Establish `h2 : (X.presheaf.germ _ x hx).hom.Flat`. Rewrite using `[← Category.comp_id (X.presheaf.germ _ x hx), ← flat_iff_comp_germ (hV.basicOpen _)]`.

Conclude with `RingHom.Flat.id _`. Rewrite using `[flat_iff_comp_germ hU (x := f x) hxU, f.germ_stalkMap U x hxU, ← X.presheaf.germ_res (homOfLE (X.basicOpen_le (f.app U r))) x hx]`. Conclude with `h1.comp h2`.
-/
theorem exists_open_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (hf : f (genericPoint X) = genericPoint Y) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨r, hr, H⟩ := exists_flat_away (f.app U).hom (f.finite_app U hU)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  refine ⟨X.basicOpen (f.app U r), ⟨genericPoint X, ?_⟩, fun x hx => ?_⟩
  · rw [← Scheme.preimage_basicOpen, SetLike.mem_coe, Scheme.Hom.mem_preimage, hf]
    refine ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen r).2).mpr ?_
    rw [Set.univ_inter]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp (by simpa using hr)
  · have := hV.isLocalization_basicOpen (f.app U r)
    have h1 := H Γ(X, X.basicOpen (f.app U r))
    have hxU : x ∈ f ⁻¹ᵁ U := X.basicOpen_le _ hx
    have h2 : (X.presheaf.germ _ x hx).hom.Flat := by
      rw [← Category.comp_id (X.presheaf.germ _ x hx), ← flat_iff_comp_germ (hV.basicOpen _)]
      exact RingHom.Flat.id _
    rw [flat_iff_comp_germ hU (x := f x) hxU, f.germ_stalkMap U x hxU,
      ← X.presheaf.germ_res (homOfLE (X.basicOpen_le (f.app U r))) x hx]
    exact h1.comp h2

end FiniteEndFlat

open UnramifiedEndFlat FiniteEndFlat in

/- English proof (translation)
Use `LocallyOfFiniteType.jacobsonSpace G.hom` as an intermediate fact. Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`. Set `o : G.left` to `η[G].left (IsLocalRing.closedPoint K)`. Establish `hfo : φ.left o = o`. Establish `: η[G] ≫ φ = η[G]` using `IsMonHom.one_hom φ`.

Conclude with `congr(($this).left (IsLocalRing.closedPoint K))`. Establish `hξ` using `apply_genericPoint φ.left hfo`. Use `⟨?_, ⟨fun y => ?_⟩⟩` and prove the remaining obligations. Take `⟨W, hW, H⟩` from `exists_open_flat φ.left hξ`. Take `⟨y, hy, hyc⟩` from `nonempty_inter_closedPoints hW W.2.isLocallyClosed`.

Use `flat_of_closedPoints _ fun x hx => ?_` and prove the remaining obligations. Set `x' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2`. Set `y' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2`. Set `α` to `GrpObj.mulRight (A := G) (y'⁻¹ * x')`. Set `β` to `GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)`.

Establish `hαβ : α.hom ≫ φ = φ ≫ β.hom`. Simplify using `only [α, β]`. Generalize the expression as in `y'⁻¹ * x' = z`. Simplify using `[comp_lift_assoc]`. Establish `hα : y' ≫ α.hom = x'`.

Establish `: y' ≫ α.hom = y' * (y'⁻¹ * x')`. Simplify using `[α, comp_lift_assoc, Hom.mul_def]`. Rewrite using `[this, mul_inv_cancel_left]`. Establish `hα' : α.hom.left y = x`. Establish `h` using `congr(($hα).left (IsLocalRing.closedPoint K))`.

Rewrite using `[← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K), ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]`. Conclude with `h`. Establish `: IsIso α.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map α.hom))`. Establish `: IsIso β.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map β.hom))`. Establish `h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat`.

Rewrite using `[Scheme.Hom.stalkMap_comp]`. Conclude with `(Flat.stalkMap β.hom.left _).comp (H y hy)`. Rewrite `h1` using `[← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp]`. Rewrite using `[← hα']`. Conclude with `(RingHom.Flat.respectsIso.cancel_right_isIso (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1`.

Conclude with `(genericPoint_specializes y).mem_closed φ.left.isClosedMap.isClosed_range ⟨_, hξ⟩`.
-/
theorem flat_and_surjective_of_isFinite_grpEnd (K : Type) [Field K] [IsAlgClosed K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [IsFinite φ.left] :
    Flat φ.left ∧ Surjective φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ := apply_genericPoint φ.left hfo
  refine ⟨?_, ⟨fun y => ?_⟩⟩
  · obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
    refine flat_of_closedPoints _ fun x hx => ?_
    let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
    let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
    let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
    let β := GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)
    have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
      simp only [α, β]
      generalize y'⁻¹ * x' = z
      simp [comp_lift_assoc]
    have hα : y' ≫ α.hom = x' := by
      have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
        simp [α, comp_lift_assoc, Hom.mul_def]
      rw [this, mul_inv_cancel_left]
    have hα' : α.hom.left y = x := by
      have h := congr(($hα).left (IsLocalRing.closedPoint K))
      rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
        ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
      exact h
    have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
    have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
      rw [Scheme.Hom.stalkMap_comp]
      exact (Flat.stalkMap β.hom.left _).comp (H y hy)
    rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
    rw [← hα']
    exact (RingHom.Flat.respectsIso.cancel_right_isIso
      (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1
  · exact (genericPoint_specializes y).mem_closed φ.left.isClosedMap.isClosed_range ⟨_, hξ⟩

/- English proof (translation)
Introduce `h K _ _ A _ hA f _ _`. Use `hA.smooth` as an intermediate fact. Use `h _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact. Establish `: IsIntegral A.left` using `GeometricallyIntegral.isIntegral_of_subsingleton A.hom`. Conclude with `flat_and_surjective_of_isFinite_grpEnd K A f`.
-/
theorem flat_and_surjective_of_isFinite_abelianEnd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S),
      Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A],
      IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left →
        Flat f.left ∧ Surjective f.left := by
  intro h K _ _ A _ hA f _ _
  have := hA.smooth
  have := h _ _ A.hom hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact flat_and_surjective_of_isFinite_grpEnd K A f

end GlobalTheory
