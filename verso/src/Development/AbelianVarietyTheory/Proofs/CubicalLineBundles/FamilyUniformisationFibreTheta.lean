import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace FibreUnif

/- English proof (translation)
It suffices to establish `key : ∀ (W : Y.Opens) (f : Γ(Y, W)) (z₀ : V), ⊤ ≤ e z₀ ⁻¹ᵁ W → (∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ W) ∧ DifferentiableAt ℂ (fun z => valAt' (e z) W f) z₀ by`. Introduce `W f`. Use `⟨isOpen_iff_mem_nhds.2 fun z hz => ?_, fun z hz => (key W f z hz.2).2.differentiableWithinAt⟩` and prove the remaining obligations. Use `filter_upwards [(key W f z hz.2).1] with z' hz' using ⟨trivial, hz'⟩`. Introduce `W f z₀ hW`.

Take `⟨S, hS, hyS, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y (default : PrimeSpectrum ℂ)) trivial`. Establish `hyS' : ⊤ ≤ y ⁻¹ᵁ S` using `(top_le_preimage_iff_mem y S).2 hyS`. Establish `hey : (e z₀ ≫ φ) ≫ p = y` using `by rw [Category.assoc, H.w, ← Category.assoc, hs, Category.id_comp]`. Take `⟨U, hU, hxU, hUS⟩` from `exists_isAffineOpen_mem_and_subset (X := Z) (U := p ⁻¹ᵁ S) (x := (e z₀ ≫ φ) (default : PrimeSpectrum ℂ)) ((top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ p S).1 (hey.symm ▸ hyS')))`. Establish `hUS' : U ≤ p ⁻¹ᵁ S` using `hUS`.

Establish `hVdef : φ ⁻¹ᵁ U = φ ⁻¹ᵁ U ⊓ s ⁻¹ᵁ ⊤` using `by simp`. Establish `hV : IsAffineOpen (φ ⁻¹ᵁ U)`. Establish `: IsAffine _` using `isAffineOpen_top (Sp ℂ)`. Establish `: IsAffine _` using `hU`. Establish `: IsAffine _` using `hS`.

Conclude with `.of_isIso (Scheme.Hom.isPullback_resLE H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).isoPullback.hom`. Establish `po` using `(isIso_pushoutSection_iff H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS (isAffineOpen_top _) hU)`. Establish `hgen` using `CommRingCat.closure_range_union_range_eq_top_of_isPushout po`. Establish `hU₀ : ⊤ ≤ (e z₀ ≫ φ) ⁻¹ᵁ U` using `(top_le_preimage_iff_mem _ _).2 hxU`. Establish `hV₀ : ⊤ ≤ e z₀ ⁻¹ᵁ (φ ⁻¹ᵁ U)` using `(top_le_preimage_comp _ φ U).1 hU₀`.

Establish `hN` using `(hol U 0).1.mem_nhds (x := z₀) ⟨trivial, hU₀⟩`. Establish `hev : ∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U)` using `by filter_upwards [hN] with z hz using (top_le_preimage_comp _ φ U).1 hz.2`. Establish `hconst : ∀ (a : Γ(Y, φ ⁻¹ᵁ U)) (c : ℂ), (∀ z, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) → valAt' (e z) _ a = c) → DifferentiableAt ℂ (fun z => valAt' (e z) _ a) z₀` using `fun a c h1 => (differentiableAt_const c).congr_of_eventuallyEq (hev.mono h1)`. Establish `D : ∀ a : Γ(Y, φ ⁻¹ᵁ U), DifferentiableAt ℂ (fun z => valAt' (e z) _ a) z₀`. Introduce `a`.

Establish `ha : a ∈ Subring.closure _` using `hgen.ge (Subring.mem_top a)`. Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨b, rfl⟩ | ⟨b, rfl⟩` into its components or cases. Establish `h3 : (fun z => valAt' (e z) _ ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b)) =ᶠ[𝓝 z₀] fun z => valAt' (e z ≫ φ) U b` using `hev.mono fun z hz => valAt'_appLE _ _ _ _ _ _ hz`.

Conclude with `((hol U b).2.differentiableAt hN).congr_of_eventuallyEq h3`. Use `hconst _ (valAt' (𝟙 _) ⊤ b) (fun z hz => ?_)` and prove the remaining obligations. Rewrite using `[valAt'_appLE _ _ _ _ _ _ hz, hs]`. Consider the case `zero => exact hconst _ 0 (fun z _ => valAt'_zero _ _)`. Consider the case `one => exact hconst _ 1 (fun z hz => valAt'_one _ hz)`.

Consider the case `add x y _ _ hx hy`. Simplify using `only [valAt'_add]`. Conclude with `hx.add hy`. Consider the case `neg x _ hx`. Simplify using `only [valAt'_neg]`.

Conclude with `hx.neg`. Consider the case `mul x y _ _ hx hy`. Simplify using `only [valAt'_mul]`. Conclude with `hx.mul hy`. Take `⟨h, hhU, hh₀⟩` from `hV.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem _ W).1 hW⟩ ((top_le_preimage_iff_mem _ _).1 hV₀)`.

Establish `hD₀ : ⊤ ≤ e z₀ ⁻¹ᵁ Y.basicOpen h` using `(top_le_preimage_iff_mem _ _).2 hh₀`. Establish `hn₀ : valAt' (e z₀) _ h ≠ 0` using `(top_le_preimage_basicOpen_iff _ _ h).1 hD₀`. Establish `hev' : ∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ Y.basicOpen h` using `by filter_upwards [(D h).continuousAt.eventually_ne hn₀] with z hz`. Conclude with `(top_le_preimage_basicOpen_iff _ _ h).2 hz`. Use `⟨hev'.mono fun z hz => top_le_preimage_mono _ hhU hz, ?_⟩` and prove the remaining obligations.

Establish `hloc` using `hV.isLocalization_basicOpen h`. Take `⟨⟨a, _, n, rfl⟩, ha⟩` from `IsLocalization.surj (Submonoid.powers h) (resG Y hhU f)`. Establish `ha' : resG Y hhU f * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a` using `ha`. Establish `hb₀ : valAt' (e z₀) _ (h ^ n) ≠ 0`. Rewrite using `[valAt'_pow _ hV₀]`.

Conclude with `pow_ne_zero n hn₀`. Establish `hmul : (fun z => valAt' (e z) W f * valAt' (e z) _ (h ^ n)) =ᶠ[𝓝 z₀] fun z => valAt' (e z) _ a` using `by filter_upwards [hev'] with z hz`. Rewrite using `[← valAt'_res _ hhU f hz, ← valAt'_res _ (Y.basicOpen_le h) (h ^ n) hz, ← valAt'_mul, ha', valAt'_res _ _ _ hz]`. Use `((D a).mul ((D (h ^ n)).inv hb₀)).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hmul, (D (h ^ n)).continuousAt.eventually_ne hb₀] with z h1 h2`.

Simplify using `only [Pi.mul_apply, Pi.inv_apply]`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ h2]`. Conclude with `h1`.
-/
theorem isHolTo_of_isPullback {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y Z : Scheme.{0}} {φ : Y ⟶ Z}
    {s : Y ⟶ Sp ℂ} {p : Z ⟶ X} {y : Sp ℂ ⟶ X} (H : IsPullback φ s p y) {e : V → (Sp ℂ ⟶ Y)}
    (hs : ∀ z, e z ≫ s = 𝟙 _) (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) : IsHolTo Set.univ e := by
  suffices key : ∀ (W : Y.Opens) (f : Γ(Y, W)) (z₀ : V), ⊤ ≤ e z₀ ⁻¹ᵁ W →
      (∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ W) ∧ DifferentiableAt ℂ (fun z => valAt' (e z) W f) z₀ by
    intro W f
    refine ⟨isOpen_iff_mem_nhds.2 fun z hz => ?_, fun z hz => (key W f z hz.2).2.differentiableWithinAt⟩
    filter_upwards [(key W f z hz.2).1] with z' hz' using ⟨trivial, hz'⟩
  intro W f z₀ hW
  obtain ⟨S, hS, hyS, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyS' : ⊤ ≤ y ⁻¹ᵁ S := (top_le_preimage_iff_mem y S).2 hyS
  have hey : (e z₀ ≫ φ) ≫ p = y := by rw [Category.assoc, H.w, ← Category.assoc, hs, Category.id_comp]
  obtain ⟨U, hU, hxU, hUS⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := p ⁻¹ᵁ S)
    (x := (e z₀ ≫ φ) (default : PrimeSpectrum ℂ))
    ((top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ p S).1 (hey.symm ▸ hyS')))
  have hUS' : U ≤ p ⁻¹ᵁ S := hUS
  have hVdef : φ ⁻¹ᵁ U = φ ⁻¹ᵁ U ⊓ s ⁻¹ᵁ ⊤ := by simp
  have hV : IsAffineOpen (φ ⁻¹ᵁ U) := by
    have : IsAffine _ := isAffineOpen_top (Sp ℂ)
    have : IsAffine _ := hU
    have : IsAffine _ := hS
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS (isAffineOpen_top _) hU)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hU₀ : ⊤ ≤ (e z₀ ≫ φ) ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hV₀ : ⊤ ≤ e z₀ ⁻¹ᵁ (φ ⁻¹ᵁ U) := (top_le_preimage_comp _ φ U).1 hU₀
  have hN := (hol U 0).1.mem_nhds (x := z₀) ⟨trivial, hU₀⟩
  have hev : ∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
    filter_upwards [hN] with z hz using (top_le_preimage_comp _ φ U).1 hz.2
  have hconst : ∀ (a : Γ(Y, φ ⁻¹ᵁ U)) (c : ℂ), (∀ z, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) → valAt' (e z) _ a = c) →
      DifferentiableAt ℂ (fun z => valAt' (e z) _ a) z₀ := fun a c h1 =>
    (differentiableAt_const c).congr_of_eventuallyEq (hev.mono h1)
  have D : ∀ a : Γ(Y, φ ⁻¹ᵁ U), DifferentiableAt ℂ (fun z => valAt' (e z) _ a) z₀ := by
    intro a
    have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · have h3 : (fun z => valAt' (e z) _ ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b)) =ᶠ[𝓝 z₀]
            fun z => valAt' (e z ≫ φ) U b := hev.mono fun z hz => valAt'_appLE _ _ _ _ _ _ hz
        exact ((hol U b).2.differentiableAt hN).congr_of_eventuallyEq h3
      · refine hconst _ (valAt' (𝟙 _) ⊤ b) (fun z hz => ?_)
        rw [valAt'_appLE _ _ _ _ _ _ hz, hs]
    | zero => exact hconst _ 0 (fun z _ => valAt'_zero _ _)
    | one => exact hconst _ 1 (fun z hz => valAt'_one _ hz)
    | add x y _ _ hx hy =>
      simp only [valAt'_add]
      exact hx.add hy
    | neg x _ hx =>
      simp only [valAt'_neg]
      exact hx.neg
    | mul x y _ _ hx hy =>
      simp only [valAt'_mul]
      exact hx.mul hy
  obtain ⟨h, hhU, hh₀⟩ := hV.exists_basicOpen_le (V := W)
    ⟨_, (top_le_preimage_iff_mem _ W).1 hW⟩ ((top_le_preimage_iff_mem _ _).1 hV₀)
  have hD₀ : ⊤ ≤ e z₀ ⁻¹ᵁ Y.basicOpen h := (top_le_preimage_iff_mem _ _).2 hh₀
  have hn₀ : valAt' (e z₀) _ h ≠ 0 := (top_le_preimage_basicOpen_iff _ _ h).1 hD₀
  have hev' : ∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ Y.basicOpen h := by
    filter_upwards [(D h).continuousAt.eventually_ne hn₀] with z hz
    exact (top_le_preimage_basicOpen_iff _ _ h).2 hz
  refine ⟨hev'.mono fun z hz => top_le_preimage_mono _ hhU hz, ?_⟩
  have hloc := hV.isLocalization_basicOpen h
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers h) (resG Y hhU f)
  have ha' : resG Y hhU f * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a := ha
  have hb₀ : valAt' (e z₀) _ (h ^ n) ≠ 0 := by
    rw [valAt'_pow _ hV₀]
    exact pow_ne_zero n hn₀
  have hmul : (fun z => valAt' (e z) W f * valAt' (e z) _ (h ^ n)) =ᶠ[𝓝 z₀] fun z => valAt' (e z) _ a := by
    filter_upwards [hev'] with z hz
    rw [← valAt'_res _ hhU f hz, ← valAt'_res _ (Y.basicOpen_le h) (h ^ n) hz, ← valAt'_mul, ha', valAt'_res _ _ _ hz]
  refine ((D a).mul ((D (h ^ n)).inv hb₀)).congr_of_eventuallyEq ?_
  filter_upwards [hmul, (D (h ^ n)).continuousAt.eventually_ne hb₀] with z h1 h2
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [eq_mul_inv_iff_mul_eq₀ h2]
  exact h1

/- English proof (translation)
Use `unit_ext fun p _ => ?_` and prove the remaining obligations. Take `⟨V, hpV, ⟨θx₀, θy₀, hx₀, hy₀⟩, hall₀⟩` from `h₀ p`. Take `⟨V', hpV', -, hall⟩` from `h p`. Choose the witnesses or unpack the hypotheses as in `rfl : V = V' := by`. Use extensionality with `q`.

Rewrite using `[Subsingleton.elim (α := Z) q p]`. Conclude with `⟨fun _ => hpV', fun _ => hpV⟩`. Establish `hτ : 𝟙 _ ≫ (Out.overRes (T` using `Over.mk t) V).hom = (Out.overRes (T := Over.mk t') V).hom ≫ f := by`. Rewrite using `[Category.id_comp, ht]`. Conclude with `(Category.assoc _ _ _).symm`.

Establish `mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι (T` using `Over.mk t') V ≫ x).left ≫ φ := by`. Rewrite using `[hx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ex]`. Both sides reduce to the same expression. Establish `mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι (T` using `Over.mk t') V ≫ y).left ≫ φ := by`. Rewrite using `[hy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ey]`.

Both sides reduce to the same expression. Take `⟨θx, hθx, mx⟩` from `exists_theta_move (T := Out.overRes (T := Over.mk t') V) (T₀ := Out.overRes (T := Over.mk t) V) hp (𝟙 _) hτ hL₀ hL w hw k _ θx₀ mvx`. Take `⟨θy, hθy, my⟩` from `exists_theta_move (T := Out.overRes (T := Over.mk t') V) (T₀ := Out.overRes (T := Over.mk t) V) hp (𝟙 _) hτ hL₀ hL w hw k _ θy₀ mvy`. Establish `hm` using `commIsOf_move (T := Out.overRes (T := Over.mk t') V) (T₀ := Out.overRes (T := Over.mk t) V) hp (𝟙 _) hτ hL₀ hL w k θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy) mx my (Out.unitRes (T := Over.mk t) V c₀) (Out.unitRes (T := Over.mk t') V c₀) (fun Z r z => by rw [C …`. Conclude with `WeilCube.germ_eq_of_unitRes (T := Over.mk t') hpV (commIsOf_unique hL θx θy _ _ (hall θx θy hθx hθy) hm)`.
-/
theorem weil_eq_of_grpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {L₀ : LB G.left} {L : LB A.left}
    (hL₀ : L₀.IsLB) (hL : L.IsLB) (w : LB.Iso L (L₀.pull φ)) (hw : w.IsGen) {Z : Scheme.{0}} [Subsingleton Z]
    {t : Z ⟶ S} {t' : Z ⟶ S'} (ht : t = t' ≫ f) (k : ℤ) (x y : Over.mk t' ⟶ A) (x₀ y₀ : Over.mk t ⟶ G)
    (ex : x₀.left = x.left ≫ φ) (ey : y₀.left = y.left ≫ φ) (c c₀ : Γ(Z, ⊤)ˣ)
    (h : Out.WeilIs A L k x y c) (h₀ : Out.WeilIs G L₀ k x₀ y₀ c₀) : c = c₀ := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hx₀, hy₀⟩, hall₀⟩ := h₀ p
  obtain ⟨V', hpV', -, hall⟩ := h p
  obtain rfl : V = V' := by
    ext q
    rw [Subsingleton.elim (α := Z) q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  have hτ : 𝟙 _ ≫ (Out.overRes (T := Over.mk t) V).hom = (Out.overRes (T := Over.mk t') V).hom ≫ f := by
    rw [Category.id_comp, ht]; exact (Category.assoc _ _ _).symm
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι (T := Over.mk t') V ≫ x).left ≫ φ := by
    rw [hx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ex]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι (T := Over.mk t') V ≫ y).left ≫ φ := by
    rw [hy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ey]; rfl
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move (T := Out.overRes (T := Over.mk t') V) (T₀ := Out.overRes (T := Over.mk t) V)
    hp (𝟙 _) hτ hL₀ hL w hw k _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move (T := Out.overRes (T := Over.mk t') V) (T₀ := Out.overRes (T := Over.mk t) V)
    hp (𝟙 _) hτ hL₀ hL w hw k _ θy₀ mvy
  have hm := commIsOf_move (T := Out.overRes (T := Over.mk t') V) (T₀ := Out.overRes (T := Over.mk t) V)
    hp (𝟙 _) hτ hL₀ hL w k θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy)
    mx my (Out.unitRes (T := Over.mk t) V c₀) (Out.unitRes (T := Over.mk t') V c₀)
    (fun Z r z => by rw [Category.comp_id]; rfl) (hall₀ θx₀ θy₀ hx₀ hy₀)
  exact WeilCube.germ_eq_of_unitRes (T := Over.mk t') hpV (commIsOf_unique hL θx θy _ _ (hall θx θy hθx hθy) hm)

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Establish `: Countable C` using `hC`. Establish `hi : Function.Injective (fun t : ℂ => (⟨t • z, h t⟩ : C))` using `fun a b hab => smul_left_injective ℂ hz (congrArg Subtype.val hab)`. Establish `: Uncountable ℂ` using `Complex.ofReal_injective.uncountable`. Conclude with `not_countable (α := ℂ) hi.countable`.
-/
theorem eq_zero_of_smul_mem_countable {V : Type} [AddCommGroup V] [Module ℂ V] {C : Set V} (hC : C.Countable) {z : V}
    (h : ∀ t : ℂ, t • z ∈ C) : z = 0 := by
  by_contra hz
  have : Countable C := hC
  have hi : Function.Injective (fun t : ℂ => (⟨t • z, h t⟩ : C)) := fun a b hab =>
    smul_left_injective ℂ hz (congrArg Subtype.val hab)
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact not_countable (α := ℂ) hi.countable

/- English proof (translation)
Introduce `w`. Establish `: (LinearMap.range F).mkQ w = 0`. Use `eq_zero_of_smul_mem_countable (hC.image (LinearMap.range F).mkQ) fun t => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `h (t • w)`. Use `⟨_, hz, ?_⟩` and prove the remaining obligations.

Establish `: (LinearMap.range F).mkQ (F z) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩`. Rewrite using `[map_sub, this, sub_zero, map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 this`.
-/
theorem surjective_of_countable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (F : V →ₗ[ℂ] W) {C : Set W} (hC : C.Countable) (h : ∀ w, ∃ z, w - F z ∈ C) : Function.Surjective F := by
  intro w
  have : (LinearMap.range F).mkQ w = 0 := by
    refine eq_zero_of_smul_mem_countable (hC.image (LinearMap.range F).mkQ) fun t => ?_
    obtain ⟨z, hz⟩ := h (t • w)
    refine ⟨_, hz, ?_⟩
    have : (LinearMap.range F).mkQ (F z) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
    rw [map_sub, this, sub_zero, map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).1 this

/- English proof (translation)
Establish `hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ n - m` using `fun k hk => by`. Take `⟨j, hj⟩` from `Complex.exp_eq_exp_iff_exists_int.1 (h k hk)`. Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `hk' : (k : ℂ) ≠ 0` using `by exact_mod_cast hk.ne'`. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`.

Establish `: ((n - m : ℤ) : ℂ) = ((k * j : ℤ) : ℂ)`. Use `push_cast`. Use `mul_left_cancel₀ h2 ?_` and prove the remaining obligations. Clear denominators, using `at hj` for the nonvanishing conditions. Take the linear combination `(2 * Real.pi * Complex.I) * hj`.

Conclude with `this` after adjusting the coercions. Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((n - m).natAbs + 1) (Nat.succ_pos _)) (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem int_eq_of_exp_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ n - m := fun k hk => by
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    refine ⟨j, ?_⟩
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have : ((n - m : ℤ) : ℂ) = ((k * j : ℤ) : ℂ) := by
      push_cast
      refine mul_left_cancel₀ h2 ?_
      field_simp at hj
      linear_combination (2 * Real.pi * Complex.I) * hj
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((n - m).natAbs + 1) (Nat.succ_pos _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

/- English proof (translation)
Introduce `a b h` and use `by have := congrArg (fun u : Γ(Sp R, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h exact Units.ext (by simpa [unitOn] using this)`.
-/
theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun a b h => by
  have := congrArg (fun u : Γ(Sp R, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h
  exact Units.ext (by simpa [unitOn] using this)

/- English proof (translation)
Introduce `U f`. Establish `hc : Differentiable ℂ (fun z : W => (b, z))` using `by fun_prop`. Use `⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩⟩` and prove the remaining obligations. Use `(h U f).1.preimage hc.continuous using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`.

Conclude with `⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩`.
-/
theorem isHolTo_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {y : V × W → (Sp ℂ ⟶ X)} (h : IsHolTo (Set.univ ×ˢ Set.univ) y) (b : V) :
    IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  have hc : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩⟩
  convert (h U f).1.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

end FibreUnif

open FibreUnif in

/- English proof (translation)
Introduce `hT _ E _ _ _ H D l Xo σ g ty FU i Pe hP P φ hp ⟨w, hw⟩`. Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, hth, hEf, -, hweil⟩` from `hT P rig hrig`. Establish `inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y` using `fun x y h => Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))`. Establish `lift : ∀ x₀ : Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left` using `fun x₀ => ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _), hp.1.lift_fst _ _ _⟩`.

Use `choose Φ hΦ using lift`. Establish `Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y` using `fun x y => inj _ _ (by`. Rewrite using `[hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]`. Conclude with `mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)`. Establish `Φinj : Function.Injective Φ` using `fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])`.

Establish `Φsurj : Function.Surjective Φ` using `fun x => ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩`. Establish `Φone : Φ 1 = 1`. Use `Φmul 1 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_mul.1 this`.

Establish `holG : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (FU.ex i Pe z).left)`. Establish `h` using `(FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2`. Conclude with `isHolTo_slice h 0`. Establish `hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (FU.ex i Pe z)).left)` using `isHolTo_of_isPullback hp.1 (e := fun z => (Φ (FU.ex i Pe z)).left) (fun z => Over.w (Φ (FU.ex i Pe z))) (by simpa only [hΦ] using holG)`. Take `⟨F, hF, -⟩` from `GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u ht₁ ht₂ (fun z => Φ (FU.ex i Pe z)) (fun z z' => by rw [FU.ex_add i Pe hP, Φmul]) hol`.

Establish `hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range` using `fun z => by`. Rewrite using `[← u.ker, hF, ← FU.ex_ker i Pe hP, ← Φone, Φinj.eq_iff]`. Establish `cΛ : (u.Λ : Set (Fin P.g → ℂ)).Countable`. Use `u.discrete` as an intermediate fact. Conclude with `(countable_of_Lindelof_of_discrete : Countable u.Λ)`.

Establish `cP : (Pe.range : Set (Fin g → ℂ)).Countable`. Use `hP.2.2.1` as an intermediate fact. Conclude with `(countable_of_Lindelof_of_discrete : Countable Pe.range)`. Establish `Finj : Function.Injective F` using `(injective_iff_map_eq_zero F).2 fun z hz => eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)`. Establish `Fsurj : Function.Surjective F` using `surjective_of_countable F cΛ fun v => by`.

Take `⟨x₀, hx₀⟩` from `Φsurj (u.ex v)`. Take `⟨z, rfl⟩` from `FU.ex_onto i Pe hP x₀`. Use `⟨z, (u.ker _).1 ?_⟩` and prove the remaining obligations. Use `u.ex_add (v - F z) (F z)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, hF, hx₀]`.

Conclude with `right_eq_mul.1 this`. Establish `hex : ∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left` using `fun z => by rw [hF, hΦ]`. Use `⟨u, Hm, χ, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, ht₁, ht₂, hth, hex, hΛ, fun a b => ?_⟩` and prove the remaining obligations. Set `a' : u.Λ` to `⟨F (Pe a), (hΛ _).2 ⟨a, rfl⟩⟩`. Set `b' : u.Λ` to `⟨F (Pe b), (hΛ _).2 ⟨b, rfl⟩⟩`.

Use `(hEf a' b').symm.trans (congrArg _ (int_eq_of_exp_eq fun k hk => ?_))` and prove the remaining obligations. Establish `h₁` using `hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Establish `h₂` using `FU.ex_weil i Pe hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Establish `: Subsingleton (Sp ℂ)` using `inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))`. Establish `h₃` using `weil_eq_of_grpPullback hp Xo.univ.t.PP.isLB P.isLB w hw (Z := Sp ℂ) (t := FU.u i Pe) (t' := 𝟙 _) (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F (Pe a))) (u.ex ((k : ℂ)⁻¹ • F (Pe b))) _ _ (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂`.

Conclude with `congrArg Units.val (unitOn_injective h₃)`.
-/
theorem familyUnif_fibre_theta : ThetaUnifAV → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)),
  IsPeriod (FU.Di i) ty Pe → ∀ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ Xo.univ.t.G.left),
  IsGrpPullback P.A Xo.univ.t.G (FU.u i Pe) φ → LBIso P.L (Xo.univ.t.PP.L.pull φ) →
  ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)),
    u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
    (∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left) ∧ (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
    ∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = (FU.Di i).EF a b := by
  intro hT _ E _ _ _ H D l Xo σ g ty FU i Pe hP P φ hp ⟨w, hw⟩
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, hth, hEf, -, hweil⟩ := hT P rig hrig
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y := fun x y h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))
  have lift : ∀ x₀ : Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)
  have Φinj : Function.Injective Φ := fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φsurj : Function.Surjective Φ := fun x =>
    ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have holG : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (FU.ex i Pe z).left) := by
    have h := (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    exact isHolTo_slice h 0
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (FU.ex i Pe z)).left) :=
    isHolTo_of_isPullback hp.1 (e := fun z => (Φ (FU.ex i Pe z)).left) (fun z => Over.w (Φ (FU.ex i Pe z)))
      (by simpa only [hΦ] using holG)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u ht₁ ht₂ (fun z => Φ (FU.ex i Pe z))
    (fun z z' => by rw [FU.ex_add i Pe hP, Φmul]) hol
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range := fun z => by
    rw [← u.ker, hF, ← FU.ex_ker i Pe hP, ← Φone, Φinj.eq_iff]
  have cΛ : (u.Λ : Set (Fin P.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cP : (Pe.range : Set (Fin g → ℂ)).Countable := by
    have := hP.2.2.1
    exact (countable_of_Lindelof_of_discrete : Countable Pe.range)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := surjective_of_countable F cΛ fun v => by
    obtain ⟨x₀, hx₀⟩ := Φsurj (u.ex v)
    obtain ⟨z, rfl⟩ := FU.ex_onto i Pe hP x₀
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hx₀] at this
    exact right_eq_mul.1 this
  have hex : ∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left := fun z => by rw [hF, hΦ]
  refine ⟨u, Hm, χ, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, ht₁, ht₂, hth, hex, hΛ, fun a b => ?_⟩
  let a' : u.Λ := ⟨F (Pe a), (hΛ _).2 ⟨a, rfl⟩⟩
  let b' : u.Λ := ⟨F (Pe b), (hΛ _).2 ⟨b, rfl⟩⟩
  refine (hEf a' b').symm.trans (congrArg _ (int_eq_of_exp_eq fun k hk => ?_))
  have h₁ := hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have h₂ := FU.ex_weil i Pe hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have h₃ := weil_eq_of_grpPullback hp Xo.univ.t.PP.isLB P.isLB w hw (Z := Sp ℂ) (t := FU.u i Pe) (t' := 𝟙 _)
    (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F (Pe a))) (u.ex ((k : ℂ)⁻¹ • F (Pe b))) _ _
    (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂
  exact congrArg Units.val (unitOn_injective h₃)

end GlobalTheory
