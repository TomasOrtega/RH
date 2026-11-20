import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')

namespace GlobalTheory.SchemeHomsFromPoints

/- English proof (translation)
Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace p`. Rewrite using `[dense_iff_closure_eq]`. Conclude with `closure_closedPoints`.
-/
theorem dense_closedPoints {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] :
    Dense (closedPoints X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  rw [dense_iff_closure_eq]
  exact closure_closedPoints

/- English proof (translation)
Use `ext_of_fromSpecResidueField_eq f g (terminal.from Y) (closedPoints X) (dense_closedPoints p) ?_ (terminal.hom_ext _ _)` and prove the remaining obligations. Introduce `x hx`. Establish `h` using `H (pointOfClosedPoint p x hx) (pointOfClosedPoint_comp p x hx)`. Rewrite using `[← cancel_epi (Spec.map (residueFieldIsoBase p x hx).hom)]`. Simplify `h` using `only [pointOfClosedPoint, Category.assoc]`.
-/
theorem hom_ext_of_points {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    [Y.IsSeparated] (f g : X ⟶ Y) (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g (terminal.from Y) (closedPoints X)
    (dense_closedPoints p) ?_ (terminal.hom_ext _ _)
  intro x hx
  have h := H (pointOfClosedPoint p x hx) (pointOfClosedPoint_comp p x hx)
  rw [← cancel_epi (Spec.map (residueFieldIsoBase p x hx).hom)]
  simpa only [pointOfClosedPoint, Category.assoc] using h

/- English proof (translation)
Rewrite using `[← basicOpen_eq_bot_iff]`. Assume the negation of the conclusion as `hne`. Establish `hne' : ((X.basicOpen h : X.Opens) : Set X).Nonempty`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Introduce `h0`.

Conclude with `hne (TopologicalSpace.Opens.ext h0)`. Take `⟨x, hx, hxc⟩` from `(dense_closedPoints p).inter_open_nonempty _ (X.basicOpen h).isOpen hne'`. Establish `e : ⊤ ≤ (pointOfClosedPoint p x hxc) ⁻¹ᵁ W`. Introduce `a _`. Express the relevant statement in the definitionally equal form `pointOfClosedPoint p x hxc a ∈ W`.

Conclude with `(pointOfClosedPoint_apply p x hxc a).symm ▸ X.basicOpen_le h hx`. Establish `h1` using `H _ (pointOfClosedPoint_comp p x hxc) e`. Establish `h2 : ((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h = 0`. Apply `(Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `h1`. Establish `h3` using `Scheme.basicOpen_appLE (pointOfClosedPoint p x hxc) ⊤ W e h`. Establish `h4 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ (Spec (CommRingCat.of ℂ)).basicOpen (((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h)`. Establish `h5 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ ⊤ ⊓ (pointOfClosedPoint p x hxc) ⁻¹ᵁ X.basicOpen h`. Use `⟨trivial, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `pointOfClosedPoint p x hxc _ ∈ X.basicOpen h`. Conclude with `(pointOfClosedPoint_apply p x hxc _).symm ▸ hx`. Rewrite `h5` using `[← h3]`. Conclude with `h5`. Rewrite `h4` using `[h2, Scheme.basicOpen_zero]`.

Conclude with `h4`.
-/
theorem eq_zero_of_points {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (W : X.Opens) (h : Γ(X, W))
    (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∀ e : ⊤ ≤ x ⁻¹ᵁ W, valAt x W e h = 0) : h = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have hne' : ((X.basicOpen h : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    exact hne (TopologicalSpace.Opens.ext h0)
  obtain ⟨x, hx, hxc⟩ := (dense_closedPoints p).inter_open_nonempty _ (X.basicOpen h).isOpen hne'
  have e : ⊤ ≤ (pointOfClosedPoint p x hxc) ⁻¹ᵁ W := by
    intro a _
    change pointOfClosedPoint p x hxc a ∈ W
    exact (pointOfClosedPoint_apply p x hxc a).symm ▸ X.basicOpen_le h hx
  have h1 := H _ (pointOfClosedPoint_comp p x hxc) e
  have h2 : ((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h1
  have h3 := Scheme.basicOpen_appLE (pointOfClosedPoint p x hxc) ⊤ W e h
  have h4 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
      (Spec (CommRingCat.of ℂ)).basicOpen (((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h) := by
    have h5 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
        ⊤ ⊓ (pointOfClosedPoint p x hxc) ⁻¹ᵁ X.basicOpen h := by
      refine ⟨trivial, ?_⟩
      change pointOfClosedPoint p x hxc _ ∈ X.basicOpen h
      exact (pointOfClosedPoint_apply p x hxc _).symm ▸ hx
    rw [← h3] at h5
    exact h5
  rw [h2, Scheme.basicOpen_zero] at h4
  exact h4

/- English proof (translation)
Establish `h1 : x.resLE W ⊤ e = (⊤ : (Spec R).Opens).ι ≫ x'`. Rewrite using `[← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, hx]`. Establish `: IsIso (⊤ : (Spec R).Opens).ι` using `inferInstanceAs (IsIso (Spec R).topIso.hom)`. Rewrite using `[← cancel_epi (⊤ : (Spec R).Opens).ι, Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Category.assoc, ← h1, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top, Scheme.Opens.toSpecΓ_SpecMap_appLE]`.
-/
theorem lift_toSpecΓ {X : Scheme.{0}} {R : CommRingCat.{0}} (W : X.Opens) (x : Spec R ⟶ X)
    (x' : Spec R ⟶ W) (hx : x' ≫ W.ι = x) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    x' ≫ W.toSpecΓ = Spec.map (x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso R).hom) := by
  have h1 : x.resLE W ⊤ e = (⊤ : (Spec R).Opens).ι ≫ x' := by
    rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, hx]
  have : IsIso (⊤ : (Spec R).Opens).ι := inferInstanceAs (IsIso (Spec R).topIso.hom)
  rw [← cancel_epi (⊤ : (Spec R).Opens).ι, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    ← Category.assoc, ← h1, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]

/- English proof (translation)
Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `e trivial`.
-/
theorem range_subset {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Set.range x ⊆ Set.range W.ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact e trivial

/- English proof (translation)
Substitute `hx` using the available equality. Introduce `t _`. Conclude with `(x'.base t).2`.
-/
theorem top_le_of_lift {X T : Scheme.{0}} (W : X.Opens) (x : T ⟶ X) (x' : T ⟶ W)
    (hx : x' ≫ W.ι = x) : ⊤ ≤ x ⁻¹ᵁ W := by
  subst hx
  intro t _
  exact (x'.base t).2

noncomputable def ev {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Γ(X, W) ⟶ CommRingCat.of ℂ :=
  x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom

/- English proof (translation)
Rewrite using `[valAt', dif_pos e]`. Both sides reduce to the same expression.
-/
theorem valAt'_eq {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) (h : Γ(X, W)) :
    valAt' x W h = (ev x W e).hom h := by
  rw [valAt', dif_pos e]
  rfl

/- English proof (translation)
Use `choose F hF using hf`. Establish `hF' : ∀ f w (e : ⊤ ≤ ex w ⁻¹ᵁ W), (ev (ex w) W e).hom (F f) = (ev (ey w) D (hWD w e)).hom f`. Introduce `f w e`. Rewrite using `[← valAt'_eq, ← valAt'_eq]`. Conclude with `hF f w e`.

Establish `inj : ∀ a b : Γ(X, W), (∀ w (e : ⊤ ≤ ex w ⁻¹ᵁ W), (ev (ex w) W e).hom a = (ev (ex w) W e).hom b) → a = b`. Introduce `a b hab`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_points p W _ ?_` and prove the remaining obligations. Introduce `x hx e`.

Take `⟨w, rfl⟩` from `hex x hx`. Express the relevant statement in the definitionally equal form `(ev (ex w) W e).hom (a - b) = 0`. Rewrite using `[map_sub, hab w e, sub_self]`. Set `φ : Γ(Y, D) →+* Γ(X, W)` to `{ toFun := F map_one' := inj _ _ fun w e => by rw [hF', map_one, map_one] map_mul' := fun a b => inj _ _ fun w e => by rw [hF', map_mul, map_mul, hF', hF'] map_zero' := inj _ _ fun w e => by rw [hF', map_zero, map_zero] map_add' := fun a b => inj _ _ fun w e => by rw [hF', map_ad …`. Use `⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hD.fromSpec, ?_⟩` and prove the remaining obligations.

Introduce `w x' hx'`. Establish `e` using `top_le_of_lift W (ex w) x' hx'`. Establish `e'` using `hWD w e`. Establish `hy'` using `IsOpenImmersion.lift_fac D.ι (ey w) (range_subset D (ey w) e')`. Establish `h1 : x' ≫ W.toSpecΓ = Spec.map (ev (ex w) W e)` using `lift_toSpecΓ W (ex w) x' hx' e`.

Establish `h2 : _ ≫ D.toSpecΓ = Spec.map (ev (ey w) D e')` using `lift_toSpecΓ D (ey w) _ hy' e'`. Establish `h3 : CommRingCat.ofHom φ ≫ ev (ex w) W e = ev (ey w) D e'`. Use extensionality with `f`. Conclude with `hF' f w e`. Rewrite using `[← Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, h3, ← h2, Category.assoc, hD.toSpecΓ_fromSpec, hy']`.
-/
theorem exists_local {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    (W : X.Opens) (D : Y.Opens) (hD : IsAffineOpen D)
    (hWD : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hf : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (x' : Sp ℂ ⟶ W), x' ≫ W.ι = ex w → x' ≫ g = ey w := by
  choose F hF using hf
  have hF' : ∀ f w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom (F f) = (ev (ey w) D (hWD w e)).hom f := by
    intro f w e
    rw [← valAt'_eq, ← valAt'_eq]
    exact hF f w e
  have inj : ∀ a b : Γ(X, W), (∀ w (e : ⊤ ≤ ex w ⁻¹ᵁ W),
      (ev (ex w) W e).hom a = (ev (ex w) W e).hom b) → a = b := by
    intro a b hab
    rw [← sub_eq_zero]
    refine eq_zero_of_points p W _ ?_
    intro x hx e
    obtain ⟨w, rfl⟩ := hex x hx
    change (ev (ex w) W e).hom (a - b) = 0
    rw [map_sub, hab w e, sub_self]
  let φ : Γ(Y, D) →+* Γ(X, W) :=
    { toFun := F
      map_one' := inj _ _ fun w e => by rw [hF', map_one, map_one]
      map_mul' := fun a b => inj _ _ fun w e => by rw [hF', map_mul, map_mul, hF', hF']
      map_zero' := inj _ _ fun w e => by rw [hF', map_zero, map_zero]
      map_add' := fun a b => inj _ _ fun w e => by rw [hF', map_add, map_add, hF', hF'] }
  refine ⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hD.fromSpec, ?_⟩
  intro w x' hx'
  have e := top_le_of_lift W (ex w) x' hx'
  have e' := hWD w e
  have hy' := IsOpenImmersion.lift_fac D.ι (ey w) (range_subset D (ey w) e')
  have h1 : x' ≫ W.toSpecΓ = Spec.map (ev (ex w) W e) := lift_toSpecΓ W (ex w) x' hx' e
  have h2 : _ ≫ D.toSpecΓ = Spec.map (ev (ey w) D e') := lift_toSpecΓ D (ey w) _ hy' e'
  have h3 : CommRingCat.ofHom φ ≫ ev (ex w) W e = ev (ey w) D e' := by
    ext f
    exact hF' f w e
  rw [← Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, h3, ← h2, Category.assoc,
    hD.toSpecΓ_fromSpec, hy']

/- English proof (translation)
Establish `hY : Y.IsSeparated` using `⟨by rw [← terminal.comp_from q]; infer_instance⟩`. Use `choose W D hD hW hWD hf using H`. Use `choose g hg using fun z => exists_local p ex ey hex (W z) (D z) (hD z) (hWD z) (hf z)`. Establish `hcov : TopologicalSpace.IsOpenCover W`. Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace p`.

Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`. Introduce `x₀ _`. Assume the negation of the conclusion as `hx₀`. Establish `hcl : IsClosed ((iSup W : X.Opens) : Set X)ᶜ` using `(iSup W).isOpen.isClosed_compl`. Take `⟨x, hx, hxc⟩` from `nonempty_inter_closedPoints ⟨x₀, hx₀⟩ hcl.isLocallyClosed`.

Take `⟨z, hz⟩` from `hex _ (pointOfClosedPoint_comp p x hxc)`. Apply `hx` to reduce the goal to its premises. Establish `h1 : ex z (IsLocalRing.closedPoint ℂ) ∈ W z` using `hW z (show (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ ⊤ from trivial)`. Establish `h2 : ex z (IsLocalRing.closedPoint ℂ) = x`. Rewrite using `[hz]`.

Conclude with `pointOfClosedPoint_apply p x hxc _`. Conclude with `le_iSup W z (h2 ▸ h1)`. Establish `hglue : ∀ i j, pullback.fst (W i).ι (W j).ι ≫ g i = pullback.snd (W i).ι (W j).ι ≫ g j`. Introduce `i j`. Establish `: IsReduced (pullback (W i).ι (W j).ι)` using `isReduced_of_isOpenImmersion (pullback.fst (W i).ι (W j).ι ≫ (W i).ι)`.

Use `hom_ext_of_points (pullback.fst (W i).ι (W j).ι ≫ (W i).ι ≫ p) _ _ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨w, hw⟩` from `hex (x ≫ pullback.fst (W i).ι (W j).ι ≫ (W i).ι) (by simpa using hx)`. Rewrite using `[← Category.assoc, ← Category.assoc, hg i w _ (by rw [hw, Category.assoc]), hg j w _ (by rw [hw, Category.assoc, pullback.condition])]`. Use `⟨(X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue, fun z => ?_⟩` and prove the remaining obligations.

Establish `h1` using `IsOpenImmersion.lift_fac (W z).ι (ex z) (range_subset (W z) (ex z) (hW z))`. Establish `h2 : (W z).ι ≫ (X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue = g z` using `Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover W hcov) g hglue z`. Rewrite using `[← hg z z _ h1, ← h2, ← Category.assoc, h1]`.
-/
theorem exists_hom {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {Z : Type} (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
    (hex : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
    {S : Scheme.{0}} (q : Y ⟶ S) [IsSeparated q] [IsAffine S]
    (H : ∀ z, ∃ (W : X.Opens) (D : Y.Opens), IsAffineOpen D ∧ ⊤ ≤ ex z ⁻¹ᵁ W ∧
      (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D) ∧
      ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
        valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : X ⟶ Y, ∀ z, ex z ≫ g = ey z := by
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  choose W D hD hW hWD hf using H
  choose g hg using fun z => exists_local p ex ey hex (W z) (D z) (hD z) (hWD z) (hf z)
  have hcov : TopologicalSpace.IsOpenCover W := by
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x₀ _
    by_contra hx₀
    have hcl : IsClosed ((iSup W : X.Opens) : Set X)ᶜ := (iSup W).isOpen.isClosed_compl
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints ⟨x₀, hx₀⟩ hcl.isLocallyClosed
    obtain ⟨z, hz⟩ := hex _ (pointOfClosedPoint_comp p x hxc)
    apply hx
    have h1 : ex z (IsLocalRing.closedPoint ℂ) ∈ W z :=
      hW z (show (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈ ⊤ from trivial)
    have h2 : ex z (IsLocalRing.closedPoint ℂ) = x := by
      rw [hz]
      exact pointOfClosedPoint_apply p x hxc _
    exact le_iSup W z (h2 ▸ h1)
  have hglue : ∀ i j, pullback.fst (W i).ι (W j).ι ≫ g i = pullback.snd (W i).ι (W j).ι ≫ g j := by
    intro i j
    have : IsReduced (pullback (W i).ι (W j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (W i).ι (W j).ι ≫ (W i).ι)
    refine hom_ext_of_points (pullback.fst (W i).ι (W j).ι ≫ (W i).ι ≫ p) _ _ ?_
    intro x hx
    obtain ⟨w, hw⟩ := hex (x ≫ pullback.fst (W i).ι (W j).ι ≫ (W i).ι) (by simpa using hx)
    rw [← Category.assoc, ← Category.assoc, hg i w _ (by rw [hw, Category.assoc]),
      hg j w _ (by rw [hw, Category.assoc, pullback.condition])]
  refine ⟨(X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue, fun z => ?_⟩
  have h1 := IsOpenImmersion.lift_fac (W z).ι (ex z) (range_subset (W z) (ex z) (hW z))
  have h2 : (W z).ι ≫ (X.openCoverOfIsOpenCover W hcov).glueMorphisms g hglue = g z :=
    Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover W hcov) g hglue z
  rw [← hg z z _ h1, ← h2, ← Category.assoc, h1]

end GlobalTheory.SchemeHomsFromPoints
