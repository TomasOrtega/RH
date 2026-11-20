import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe u

namespace GlobalTheory.ComplexPoints

section General

variable {K : Type u} [Field K] [IsAlgClosed K]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

/- English proof (translation)
Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace p`. Take `⟨y, hyZ, hy⟩` from `nonempty_inter_closedPoints hne hZ`. Establish `hy : IsClosed {y}` using `hy`. Conclude with `⟨pointOfClosedPoint p y hy, pointOfClosedPoint_comp p y hy, fun a => by rw [pointOfClosedPoint_apply]; exact hyZ⟩`.
-/
theorem _root_.GlobalTheory.ComplexPoints.exists_point_mem {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ ∧ ∀ a, x a ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨y, hyZ, hy⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed {y} := hy
  exact ⟨pointOfClosedPoint p y hy, pointOfClosedPoint_comp p y hy,
    fun a => by rw [pointOfClosedPoint_apply]; exact hyZ⟩

/- English proof (translation)
Take `⟨z, hz⟩` from `hne`. Take `⟨w, hw⟩` from `(pullback.fst p t).surjective z`. Take `⟨y, hy, hyZ⟩` from `exists_point_mem (pullback.snd p t) (hZ.preimage (pullback.fst p t).continuous) ⟨w, show pullback.fst p t w ∈ Z from hw ▸ hz⟩`. Use `⟨y ≫ pullback.fst p t, ?_, fun a => hyZ a⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, reassoc_of% hy]`.
-/
theorem exists_geomPoint_mem {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = t ∧ ∀ a, x a ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, hw⟩ := (pullback.fst p t).surjective z
  obtain ⟨y, hy, hyZ⟩ := exists_point_mem (pullback.snd p t)
    (hZ.preimage (pullback.fst p t).continuous) ⟨w, show pullback.fst p t w ∈ Z from hw ▸ hz⟩
  refine ⟨y ≫ pullback.fst p t, ?_, fun a => hyZ a⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hy]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩`.
-/
theorem surjective_specMap_field {k L : Type u} [Field k] [Field L] (σ : k →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) :=
  ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h (show a ∈ (⊤ : (Spec (.of L)).Opens) from trivial)`. Introduce `h b _`. Rewrite using `[Subsingleton.elim b a]`.

Conclude with `h`.
-/
theorem _root_.GlobalTheory.ComplexPoints.top_le_preimage_iff {L : Type u} [Field L] {X : Scheme.{u}}
    (x : Spec (.of L) ⟶ X) (U : X.Opens) (a : ↥(Spec (.of L))) : ⊤ ≤ x ⁻¹ᵁ U ↔ x a ∈ U := by
  constructor
  · intro h
    exact h (show a ∈ (⊤ : (Spec (.of L)).Opens) from trivial)
  · intro h b _
    rw [Subsingleton.elim b a]
    exact h

/- English proof (translation)
Introduce `z hzU`. Assume the negation of the conclusion as `hzV`. Take `⟨x, hx, hxZ⟩` from `exists_geomPoint_mem p t (Z := (U : Set X) ∩ (V : Set X)ᶜ) (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨z, hzU, hzV⟩`. Set `a : ↥(Spec (.of K))` to `IsLocalRing.closedPoint K`. Conclude with `(hxZ a).2 ((top_le_preimage_iff x V a).1 (h x hx ((top_le_preimage_iff x U a).2 (hxZ a).1)))`.
-/
theorem opens_le_of_geomPoints {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (U V : X.Opens)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro z hzU
  by_contra hzV
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨z, hzU, hzV⟩
  let a : ↥(Spec (.of K)) := IsLocalRing.closedPoint K
  exact (hxZ a).2 ((top_le_preimage_iff x V a).1 (h x hx ((top_le_preimage_iff x U a).2 (hxZ a).1)))

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hxZ⟩` from `exists_geomPoint_mem p t hZ.isOpen_compl.isLocallyClosed (Set.nonempty_compl.mpr hne)`. Take `⟨a, ha⟩` from `h x hx`. Conclude with `hxZ a ha`.
-/
theorem closed_eq_univ_of_geomPoints {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ∃ a, x a ∈ Z) : Z = Set.univ := by
  by_contra hne
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t hZ.isOpen_compl.isLocallyClosed
    (Set.nonempty_compl.mpr hne)
  obtain ⟨a, ha⟩ := h x hx
  exact hxZ a ha

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hns`. Establish `hne : (Set.range ψ)ᶜ.Nonempty`. Rewrite using `[Set.nonempty_compl]`. Introduce `hr`.

Conclude with `hns (Set.range_eq_univ.mp hr)`. Establish `hP : (pullback.fst p t ⁻¹' (Set.range ψ)ᶜ).Nonempty`. Take `⟨a, ha⟩` from `hne`. Take `⟨z, hz⟩` from `(pullback.fst p t).surjective a`. Conclude with `⟨z, by simpa [hz] using ha⟩`.

Take `⟨y, hy1, hy2⟩` from `_root_.GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd p t) (hψ.isOpen_compl.preimage (pullback.fst p t).continuous).isLocallyClosed hP`. Take `⟨w, hw⟩` from `h (y ≫ pullback.fst p t) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hy1, Category.id_comp])`. Take `⟨a⟩` from `(inferInstance : Nonempty (Spec (.of K)))`. Apply `hy2 a` to reduce the goal to its premises.

Conclude with `⟨w a, by rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]⟩`.
-/
theorem _root_.GlobalTheory.ComplexPoints.surjective_of_geomPoints_lift {A B S : Scheme.{u}} (p : A ⟶ S)
    [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Spec (.of K) ⟶ A, x ≫ p = t → ∃ y : Spec (.of K) ⟶ B, y ≫ ψ = x) :
    Surjective ψ := by
  constructor
  by_contra hns
  have hne : (Set.range ψ)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hr
    exact hns (Set.range_eq_univ.mp hr)
  have hP : (pullback.fst p t ⁻¹' (Set.range ψ)ᶜ).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨z, hz⟩ := (pullback.fst p t).surjective a
    exact ⟨z, by simpa [hz] using ha⟩
  obtain ⟨y, hy1, hy2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd p t)
    (hψ.isOpen_compl.preimage (pullback.fst p t).continuous).isLocallyClosed hP
  obtain ⟨w, hw⟩ := h (y ≫ pullback.fst p t) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy1, Category.id_comp])
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of K)))
  apply hy2 a
  exact ⟨w a, by rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]⟩

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

/- English proof (translation)
Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace p`. Use `ext_of_fromSpecResidueField_eq f g q (closedPoints X) (dense_iff_closure_eq.mpr closure_closedPoints) ?_ hfg` and prove the remaining obligations. Introduce `y hy`. Establish `e` using `h (pointOfClosedPoint p y hy) (pointOfClosedPoint_comp p y hy)`. Unfold `pointOfClosedPoint at e`.

Simplify using `only [Category.assoc] at e`. Conclude with `(cancel_epi _).mp e`.
-/
theorem _root_.GlobalTheory.ComplexPoints.hom_ext_of_points {X Y S : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [LocallyOfFiniteType p]
    [IsReduced X] (q : Y ⟶ S) [IsSeparated q] {f g : X ⟶ Y} (hfg : f ≫ q = g ≫ q)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine ext_of_fromSpecResidueField_eq f g q (closedPoints X)
    (dense_iff_closure_eq.mpr closure_closedPoints) ?_ hfg
  intro y hy
  have e := h (pointOfClosedPoint p y hy) (pointOfClosedPoint_comp p y hy)
  unfold pointOfClosedPoint at e
  simp only [Category.assoc] at e
  exact (cancel_epi _).mp e

end General

variable {X Y : Scheme.{0}}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

/- English proof (translation)
Establish `e : x ⁻¹ᵁ X.basicOpen f = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).basicOpen (x.appLE U ⊤ h f)`. Rewrite using `[Scheme.basicOpen_appLE, top_inf_eq]`. Rewrite using `[e]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt`. Prove the components needed by the constructor for the conclusion.

Introduce `hs h0`. Establish `hz : x.appLE U ⊤ h f = 0`. Use `congrArg (Scheme.ΓSpecIso (.of ℂ)).inv.hom h0` as an intermediate fact. Simplify using `using this`. Rewrite `hs` using `[hz, Scheme.basicOpen_zero]`.

Take `⟨a⟩` from `(inferInstance : Nonempty (Spec (.of ℂ)))`. Conclude with `(hs (show a ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)).elim`. Introduce `hne`. Establish `hu : IsUnit (x.appLE U ⊤ h f)`. Use `(isUnit_iff_ne_zero.mpr hne).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom` as an intermediate fact.

Simplify using `using this`. Rewrite using `[Scheme.basicOpen_of_isUnit _ hu]`.
-/
theorem _root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt x U h f ≠ 0 := by
  have e : x ⁻¹ᵁ X.basicOpen f = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).basicOpen (x.appLE U ⊤ h f) := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  rw [e]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  constructor
  · intro hs h0
    have hz : x.appLE U ⊤ h f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at hs
    obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
    exact (hs (show a ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)).elim
  · intro hne
    have hu : IsUnit (x.appLE U ⊤ h f) := by
      have := (isUnit_iff_ne_zero.mpr hne).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
      simpa using this
    rw [Scheme.basicOpen_of_isUnit _ hu]

/- English proof (translation)
Establish `hU : U ≤ X.basicOpen f` using `opens_le_of_geomPoints p (𝟙 _) U _ fun x hx hxU => (top_le_preimage_basicOpen_iff x U hxU f).2 (h x hxU hx)`. Conclude with `X.toRingedSpace.isUnit_of_isUnit_germ U f fun y hy => (X.mem_basicOpen f y hy).1 (hU hy)`.
-/
theorem isUnit_of_valAt_ne_zero (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f ≠ 0) : IsUnit f := by
  have hU : U ≤ X.basicOpen f := opens_le_of_geomPoints p (𝟙 _) U _ fun x hx hxU =>
    (top_le_preimage_basicOpen_iff x U hxU f).2 (h x hxU hx)
  exact X.toRingedSpace.isUnit_of_isUnit_germ U f fun y hy => (X.mem_basicOpen f y hy).1 (hU hy)

/- English proof (translation)
Use `eq_zero_of_basicOpen_eq_bot f (le_bot_iff.1 (opens_le_of_geomPoints p (𝟙 _) _ _ ?_))` and prove the remaining obligations. Introduce `x hx hxf`. Establish `hxU : ⊤ ≤ x ⁻¹ᵁ U` using `fun a ha => X.basicOpen_le f (hxf ha)`. Conclude with `absurd (h x hxU hx) ((top_le_preimage_basicOpen_iff x U hxU f).1 hxf)`.
-/
theorem eq_zero_of_valAt_eq_zero (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = 0) : f = 0 := by
  refine eq_zero_of_basicOpen_eq_bot f (le_bot_iff.1 (opens_le_of_geomPoints p (𝟙 _) _ _ ?_))
  intro x hx hxf
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := fun a ha => X.basicOpen_le f (hxf ha)
  exact absurd (h x hxU hx) ((top_le_preimage_basicOpen_iff x U hxU f).1 hxf)

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_valAt_eq_zero p U _ fun x hx hp => ?_` and prove the remaining obligations. Use `h x hx hp` as an intermediate fact. Unfold `valAt at this ⊢`. Rewrite using `[map_sub, map_sub, this, sub_self]`.
-/
theorem eq_of_valAt_eq (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = valAt x U hx g) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_valAt_eq_zero p U _ fun x hx hp => ?_
  have := h x hx hp
  unfold valAt at this ⊢
  rw [map_sub, map_sub, this, sub_self]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
/- English proof (translation)
Introduce `y hyU`. Assume the negation of the conclusion as `hyV`. Take `⟨x, hx1, hx2⟩` from `_root_.GlobalTheory.ComplexPoints.exists_point_mem (K := ℂ) p (Z := (U : Set X) ∩ (V : Set X)ᶜ) (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hyU, hyV⟩`. Take `⟨a⟩` from `(inferInstance : Nonempty (Spec (.of ℂ)))`. Establish `hU : ⊤ ≤ x ⁻¹ᵁ U` using `(_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x U a).mpr (hx2 a).1`.

Conclude with `(hx2 a).2 ((_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x V a).mp (h x hx1 hU))`.
-/
private theorem opens_le_of_forall_complex_section (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro y hyU
  by_contra hyV
  obtain ⟨x, hx1, hx2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (K := ℂ) p
    (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hyU, hyV⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x U a).mpr (hx2 a).1
  exact (hx2 a).2 ((_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x V a).mp (h x hx1 hU))

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises. Use `eq_bot_iff.mpr (opens_le_of_forall_complex_section p _ ⊥ fun x hx hb => ?_)` and prove the remaining obligations. Establish `hU : ⊤ ≤ x ⁻¹ᵁ U` using `hb.trans fun b hb' => X.basicOpen_le (f - g) hb'`. Establish `hne` using `(_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU (f - g)).mp hb`.

Establish `he` using `h x hx hU`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at he`. Rewrite `he` using `[dif_pos hU, dif_pos hU]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hne he`. Rewrite `hne` using `[map_sub, map_sub, he, sub_self]`.

Conclude with `(hne rfl).elim`.
-/
theorem _root_.GlobalTheory.ComplexPoints.eq_of_valAt'_eq (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U g) :
    f = g := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  refine eq_bot_iff.mpr (opens_le_of_forall_complex_section p _ ⊥ fun x hx hb => ?_)
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans fun b hb' => X.basicOpen_le (f - g) hb'
  have hne := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU (f - g)).mp hb
  have he := h x hx hU
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at he
  rw [dif_pos hU, dif_pos hU] at he
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hne he
  rw [map_sub, map_sub, he, sub_self] at hne
  exact (hne rfl).elim

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

/- English proof (translation)
Establish `hle : U ≤ X.basicOpen f` using `opens_le_of_forall_complex_section p U _ fun x hx hU => by`. Use `h x hx hU` as an intermediate fact. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at this`. Rewrite `this` using `[dif_pos hU]`. Conclude with `(_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU f).mpr this`.

Establish `hu` using `(X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE hle).op).hom`. Establish `hid : (homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hle).op = 𝟙 (Opposite.op U)` using `Subsingleton.elim _ _`. Use `hu using 1` and compare the differences between its conclusion and the goal. Use `erw [← CommRingCat.comp_apply, ← Functor.map_comp, hid, CategoryTheory.Functor.map_id, CommRingCat.id_apply]`.
-/
theorem _root_.GlobalTheory.ComplexPoints.isUnit_of_valAt'_ne_zero (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f ≠ 0) : IsUnit f := by
  have hle : U ≤ X.basicOpen f := opens_le_of_forall_complex_section p U _ fun x hx hU => by
    have := h x hx hU
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at this
    rw [dif_pos hU] at this
    exact (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU f).mpr this
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map
    (X.presheaf.map (homOfLE hle).op).hom
  have hid : (homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hle).op = 𝟙 (Opposite.op U) :=
    Subsingleton.elim _ _
  convert hu using 1
  erw [← CommRingCat.comp_apply, ← Functor.map_comp, hid, CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]

/- English proof (translation)
The claim follows from `hom_ext_of_points p q (hf.trans hg.symm) h`.
-/
theorem hom_ext_of_complexPoints (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (q : Y ⟶ Sp ℂ) [IsSeparated q] {f g : X ⟶ Y} (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g :=
  hom_ext_of_points p q (hf.trans hg.symm) h

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `_root_.GlobalTheory.ComplexPoints.hom_ext_of_points (K := ℂ) A.hom B.hom (by rw [Over.w f, Over.w g]) fun x hx => ?_` and prove the remaining obligations. Use `h (Over.homMk x (by simpa using hx))` as an intermediate fact. Simplify using `using congrArg (fun k => k.left) this`.
-/
theorem _root_.GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints {A B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)} [LocallyOfFiniteType A.hom]
    [IsReduced A.left] [IsSeparated B.hom] {f g : A ⟶ B}
    (h : ∀ x : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ A, x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine _root_.GlobalTheory.ComplexPoints.hom_ext_of_points (K := ℂ) A.hom B.hom
    (by rw [Over.w f, Over.w g]) fun x hx => ?_
  have := h (Over.homMk x (by simpa using hx))
  simpa using congrArg (fun k => k.left) this

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

/- English proof (translation)
The claim follows from `opens_le_of_forall_complex_section p U V h`.
-/
theorem _root_.GlobalTheory.ComplexPoints.opens_le_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p] (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V :=
  opens_le_of_forall_complex_section p U V h

/- English proof (translation)
The claim follows from `top_le_iff.1 (opens_le_of_complexPoints p ⊤ U fun x hx _ => h x hx)`.
-/
theorem opens_eq_top_of_complexPoints (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U) : U = ⊤ :=
  top_le_iff.1 (opens_le_of_complexPoints p ⊤ U fun x hx _ => h x hx)

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

/- English proof (translation)
Use `eq_top_iff.mpr (opens_le_of_forall_complex_section p ⊤ _ fun x hx _ => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `h x hx`. Take `⟨a⟩` from `(inferInstance : Nonempty (Spec (.of ℂ)))`. Rewrite `hi`, the goal using `[_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x _ a]`. Conclude with `(le_iSup U i) hi`.
-/
theorem _root_.GlobalTheory.ComplexPoints.iSup_eq_top_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    {I : Type*} (U : I → X.Opens) (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ i, ⊤ ≤ x ⁻¹ᵁ U i) :
    ⨆ i, U i = ⊤ := by
  refine eq_top_iff.mpr (opens_le_of_forall_complex_section p ⊤ _ fun x hx _ => ?_)
  obtain ⟨i, hi⟩ := h x hx
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  rw [_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x _ a] at hi ⊢
  exact (le_iSup U i) hi

/- English proof (translation)
The claim follows from `haveI : Surjective (spMap σ) := surjective_specMap_field σ surjective_of_geomPoints_lift a (spMap σ) ψ hψ h`.
-/
theorem surjective_of_complexPoints_lift {k : Type} [Field k] (σ : k →+* ℂ) {A B : Scheme.{0}}
    (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ :=
  haveI : Surjective (spMap σ) := surjective_specMap_field σ
  surjective_of_geomPoints_lift a (spMap σ) ψ hψ h

/- English proof (translation)
Substitute `hw` using the available equality. Establish `: UniversallyClosed ψ` using `UniversallyClosed.of_comp_of_isSeparated ψ a`. Conclude with `surjective_of_complexPoints_lift σ a ψ ψ.isClosedMap.isClosed_range h`.
-/
theorem surjective_of_complexPoints_lift_of_universallyClosed {k : Type} [Field k] (σ : k →+* ℂ)
    {A B : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] [IsSeparated a] (b : B ⟶ Sp k)
    [UniversallyClosed b] (ψ : B ⟶ A) (hw : ψ ≫ a = b)
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ := by
  subst hw
  have : UniversallyClosed ψ := UniversallyClosed.of_comp_of_isSeparated ψ a
  exact surjective_of_complexPoints_lift σ a ψ ψ.isClosedMap.isClosed_range h

end GlobalTheory.ComplexPoints

namespace GlobalTheory

/- English proof (translation)
Introduce `_ p _ _ U f` and use `⟨ComplexPoints.eq_zero_of_valAt_eq_zero p U f, ComplexPoints.isUnit_of_valAt_ne_zero p U f⟩`.
-/
theorem eq_zero_and_isUnit_of_valAt :
    ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
      (f : Γ(X, U)),
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f = 0) → f = 0) ∧
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f ≠ 0) → IsUnit f) :=
  fun _ p _ _ U f =>
    ⟨ComplexPoints.eq_zero_of_valAt_eq_zero p U f, ComplexPoints.isUnit_of_valAt_ne_zero p U f⟩

end GlobalTheory
