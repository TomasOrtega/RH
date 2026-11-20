import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ComplexPointsGroup

def IsContFamily {T : Type} [TopologicalSpace T] {X : Scheme.{0}} (e : T → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)) (O : Set ℂ), IsOpen O → IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U ∧ valAt' (e t) U f ∈ O}

variable {T : Type} [TopologicalSpace T]

/- English proof (translation)
Simplify using `using he U 0 Set.univ isOpen_univ`.
-/
theorem IsContFamily.isOpen_mem {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens) :
    IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U} := by
  simpa using he U 0 Set.univ isOpen_univ

/- English proof (translation)
The claim follows from `(continuousOn_open_iff (he.isOpen_mem U)).2 fun O hO => he U f O hO`.
-/
theorem IsContFamily.continuousOn {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens)
    (f : Γ(X, U)) : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ U} :=
  (continuousOn_open_iff (he.isOpen_mem U)).2 fun O hO => he U f O hO

variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv

/- English proof (translation)
Introduce `U f O hO`. Use `he (φ ⁻¹ᵁ U) ((φ.app U).hom f) O hO` as an intermediate fact. Simplify using `only [(hv X _).2.2.2.1] at this`. Conclude with `this`.
-/
theorem IsContFamily.comp {X Y : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (φ : X ⟶ Y) :
    IsContFamily (fun t => e t ≫ φ) := by
  intro U f O hO
  have := he (φ ⁻¹ᵁ U) ((φ.app U).hom f) O hO
  simp only [(hv X _).2.2.2.1] at this
  exact this

/- English proof (translation)
Introduce `U f O hO`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `t₀ ⟨hU, hf⟩`. Take `⟨P, hP, h₀, hopen, hcont⟩` from `h t₀`. Take `⟨s, hsU, hs₀⟩` from `hP.exists_basicOpen_le (V := U) ⟨_, ((hv X _).1 U).1 hU⟩ (((hv X _).1 P).1 h₀)`.

Take `⟨n, g, hg⟩` from `exists_eq_pow_mul_of_isAffineOpen X P hP s (resG X hsU f)`. Establish `key : ∀ t, ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s → valAt' (e t) U f = valAt' (e t) P g / valAt' (e t) P s ^ n`. Introduce `t ht`. Establish `hne` using `((hv X (e t)).2.2.2.2.1 P s).1 ht`. Take `⟨ev, hev⟩` from `(hv X (e t)).2.1 _ ht`.

Establish `h1` using `(hv X (e t)).2.2.1 P _ (X.basicOpen_le s) g ht`. Establish `h2` using `(hv X (e t)).2.2.1 P _ (X.basicOpen_le s) s ht`. Establish `h3` using `(hv X (e t)).2.2.1 U _ hsU f ht`. Establish `hg' : resG X (X.basicOpen_le s) g = resG X (X.basicOpen_le s) s ^ n * resG X hsU f` using `hg`. Rewrite using `[eq_div_iff (pow_ne_zero n hne), ← h1, ← h2, ← h3, hg', hev, hev, hev, map_mul, map_pow, mul_comm]`.

Establish `hN : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} = {t | ⊤ ≤ e t ⁻¹ᵁ P} ∩ (fun t => valAt' (e t) P s) ⁻¹' {0}ᶜ`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce `ht`. Conclude with `⟨le_trans ht ((e t).preimage_mono (X.basicOpen_le s)), ((hv X (e t)).2.2.2.2.1 P s).1 ht⟩`.

Introduce `ht`. Conclude with `((hv X (e t)).2.2.2.2.1 P s).2 ht.2`. Establish `hNo : IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s}`. Rewrite using `[hN]`. Conclude with `(hcont s).isOpen_inter_preimage hopen isOpen_compl_singleton`.

Establish `hsub : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ⊆ {t | ⊤ ≤ e t ⁻¹ᵁ P}`. Rewrite using `[hN]`. Conclude with `Set.inter_subset_left`. Establish `hc : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s}`. Use `ContinuousOn.congr (f := fun t => valAt' (e t) P g / valAt' (e t) P s ^ n) ?_ key` and prove the remaining obligations.

Conclude with `((hcont g).mono hsub).div (((hcont s).mono hsub).pow n) fun t ht => pow_ne_zero n (((hv X (e t)).2.2.2.2.1 P s).1 ht)`. Use `⟨{t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ∩ (fun t => valAt' (e t) U f) ⁻¹' O, ?_, hc.isOpen_inter_preimage hNo hO, ((hv X _).1 _).2 hs₀, hf⟩` and prove the remaining obligations. Introduce and unpack `t ⟨ht, hto⟩`. Conclude with `⟨le_trans ht ((e t).preimage_mono hsU), hto⟩`.
-/
theorem isContFamily_of_affine {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)}
    (h : ∀ t₀, ∃ P : X.Opens, IsAffineOpen P ∧ ⊤ ≤ e t₀ ⁻¹ᵁ P ∧ IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ P} ∧
      ∀ g : Γ(X, P), ContinuousOn (fun t => valAt' (e t) P g) {t | ⊤ ≤ e t ⁻¹ᵁ P}) :
    IsContFamily e := by
  intro U f O hO
  rw [isOpen_iff_forall_mem_open]
  rintro t₀ ⟨hU, hf⟩
  obtain ⟨P, hP, h₀, hopen, hcont⟩ := h t₀
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, ((hv X _).1 U).1 hU⟩ (((hv X _).1 P).1 h₀)
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen X P hP s (resG X hsU f)
  have key : ∀ t, ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s →
      valAt' (e t) U f = valAt' (e t) P g / valAt' (e t) P s ^ n := by
    intro t ht
    have hne := ((hv X (e t)).2.2.2.2.1 P s).1 ht
    obtain ⟨ev, hev⟩ := (hv X (e t)).2.1 _ ht
    have h1 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) g ht
    have h2 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) s ht
    have h3 := (hv X (e t)).2.2.1 U _ hsU f ht
    have hg' : resG X (X.basicOpen_le s) g = resG X (X.basicOpen_le s) s ^ n * resG X hsU f := hg
    rw [eq_div_iff (pow_ne_zero n hne), ← h1, ← h2, ← h3, hg', hev, hev, hev, map_mul, map_pow, mul_comm]
  have hN : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} =
      {t | ⊤ ≤ e t ⁻¹ᵁ P} ∩ (fun t => valAt' (e t) P s) ⁻¹' {0}ᶜ := by
    ext t
    constructor
    · intro ht
      exact ⟨le_trans ht ((e t).preimage_mono (X.basicOpen_le s)), ((hv X (e t)).2.2.2.2.1 P s).1 ht⟩
    · intro ht
      exact ((hv X (e t)).2.2.2.2.1 P s).2 ht.2
  have hNo : IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    rw [hN]
    exact (hcont s).isOpen_inter_preimage hopen isOpen_compl_singleton
  have hsub : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ⊆ {t | ⊤ ≤ e t ⁻¹ᵁ P} := by
    rw [hN]; exact Set.inter_subset_left
  have hc : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    refine ContinuousOn.congr (f := fun t => valAt' (e t) P g / valAt' (e t) P s ^ n) ?_ key
    exact ((hcont g).mono hsub).div (((hcont s).mono hsub).pow n)
      fun t ht => pow_ne_zero n (((hv X (e t)).2.2.2.2.1 P s).1 ht)
  refine ⟨{t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ∩ (fun t => valAt' (e t) U f) ⁻¹' O, ?_,
    hc.isOpen_inter_preimage hNo hO, ((hv X _).1 _).2 hs₀, hf⟩
  rintro t ⟨ht, hto⟩
  exact ⟨le_trans ht ((e t).preimage_mono hsU), hto⟩

/- English proof (translation)
Rewrite using `[← (hv X x).2.2.2.1, ← (hv X x).2.2.1 _ V h _ hx]`. Both sides reduce to the same expression.
-/
theorem valAt'_appLE {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(Y, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V h).hom f) = valAt' (x ≫ φ) U f := by
  rw [← (hv X x).2.2.2.1, ← (hv X x).2.2.1 _ V h _ hx]
  rfl

/- English proof (translation)
Use `isContFamily_of_affine hv fun t₀ => ?_` and prove the remaining obligations. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := (e t₀ ≫ g) (default : PrimeSpectrum ℂ)) trivial`. Take `⟨V, hV, hpV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := (e t₀ ≫ iY) (default : PrimeSpectrum ℂ)) trivial`. Establish `hmem : ∀ t, ⊤ ≤ e t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) ↔ ⊤ ≤ (e t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (e t ≫ iY) ⁻¹ᵁ V`. Introduce `t`.

Rewrite using `[Scheme.Hom.preimage_inf, le_inf_iff]`. Both sides reduce to the same expression. Establish `hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V)`. Establish `: IsAffine _` using `hU`. Establish `: IsAffine _` using `hV`.

Establish `: IsAffine _` using `isAffineOpen_top S`. Conclude with `.of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).isoPullback.hom`. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV hU)`. Use `⟨_, hP, (hmem t₀).2 ⟨((hv _ _).1 _).2 hpU, ((hv _ _).1 _).2 hpV⟩, ?_, fun r => ?_⟩` and prove the remaining obligations. Simplify using `only [hmem]`.

Conclude with `(h₁.isOpen_mem U).inter (h₂.isOpen_mem V)`. Establish `hr` using `(CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)`. Proceed by induction on `hr using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨a, rfl⟩ | ⟨b, rfl⟩` into its components or cases.

Conclude with `((h₁.continuousOn U a).mono fun t ht => ((hmem t).1 ht).1).congr fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht`. Conclude with `((h₂.continuousOn V b).mono fun t ht => ((hmem t).1 ht).2).congr fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht`. Consider the case `zero`. Use `(continuousOn_const (c := (0 : ℂ))).congr fun t ht => ?_` and prove the remaining obligations. Take `⟨ev, hev⟩` from `(hv Z (e t)).2.1 _ ht`.

Simplify using `only [hev, map_zero]`. Consider the case `one`. Use `(continuousOn_const (c := (1 : ℂ))).congr fun t ht => ?_` and prove the remaining obligations. Take `⟨ev, hev⟩` from `(hv Z (e t)).2.1 _ ht`. Simplify using `only [hev, map_one]`.

Consider the case `add x y _ _ hx hy`. Use `(hx.add hy).congr fun t ht => ?_` and prove the remaining obligations. Take `⟨ev, hev⟩` from `(hv Z (e t)).2.1 _ ht`. Simplify using `only [hev, map_add, Pi.add_apply]`. Consider the case `neg x _ hx`.

Use `hx.neg.congr fun t ht => ?_` and prove the remaining obligations. Take `⟨ev, hev⟩` from `(hv Z (e t)).2.1 _ ht`. Simplify using `only [hev, map_neg, Pi.neg_apply]`. Consider the case `mul x y _ _ hx hy`. Use `(hx.mul hy).congr fun t ht => ?_` and prove the remaining obligations.

Take `⟨ev, hev⟩` from `(hv Z (e t)).2.1 _ ht`. Simplify using `only [hev, map_mul, Pi.mul_apply]`.
-/
theorem isContFamily_of_isPullback {X Y S Z : Scheme.{0}} [IsAffine S] {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S}
    {iY : Z ⟶ Y} (H : IsPullback g iY iX f) {e : T → (Sp ℂ ⟶ Z)}
    (h₁ : IsContFamily (fun t => e t ≫ g)) (h₂ : IsContFamily (fun t => e t ≫ iY)) : IsContFamily e := by
  refine isContFamily_of_affine hv fun t₀ => ?_
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (e t₀ ≫ g) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤)
    (x := (e t₀ ≫ iY) (default : PrimeSpectrum ℂ)) trivial
  have hmem : ∀ t, ⊤ ≤ e t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) ↔ ⊤ ≤ (e t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (e t ≫ iY) ⁻¹ᵁ V := by
    intro t
    rw [Scheme.Hom.preimage_inf, le_inf_iff]
    rfl
  have hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV hU)
  refine ⟨_, hP, (hmem t₀).2 ⟨((hv _ _).1 _).2 hpU, ((hv _ _).1 _).2 hpV⟩, ?_, fun r => ?_⟩
  · simp only [hmem]
    exact (h₁.isOpen_mem U).inter (h₂.isOpen_mem V)
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ((h₁.continuousOn U a).mono fun t ht => ((hmem t).1 ht).1).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
    · exact ((h₂.continuousOn V b).mono fun t ht => ((hmem t).1 ht).2).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
  | zero =>
    refine (continuousOn_const (c := (0 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_zero]
  | one =>
    refine (continuousOn_const (c := (1 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_one]
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_add, Pi.add_apply]
  | neg x _ hx =>
    refine hx.neg.congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_neg, Pi.neg_apply]
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_mul, Pi.mul_apply]

omit hv in

/- English proof (translation)
Rewrite using `[continuous_generateFrom_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h U f O hO`. Conclude with `h _ ⟨U, f, O, hO, rfl⟩`. Introduce and unpack `h _ ⟨U, f, O, hO, rfl⟩`.

Conclude with `h U f O hO`.
-/
theorem continuous_iff_isContFamily {A : Over (Sp ℂ)} (e : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)) :
    Continuous[_, TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}] e ↔
      IsContFamily (X := A.left) (fun t => (e t).left) := by
  rw [continuous_generateFrom_iff]
  constructor
  · intro h U f O hO
    exact h _ ⟨U, f, O, hO, rfl⟩
  · rintro h _ ⟨U, f, O, hO, rfl⟩
    exact h U f O hO

/- English proof (translation)
Establish `H : IsPullback (fst A B).left (snd A B).left A.hom B.hom` using `IsPullback.of_hasPullback A.hom B.hom`. Use `isContFamily_of_isPullback hv H ?_ ?_` and prove the remaining obligations. Use `ha using 2 with t` and compare the differences between its conclusion and the goal. Conclude with `congrArg CommaMorphism.left (lift_fst (a t) (b t))`. Use `hb using 2 with t` and compare the differences between its conclusion and the goal.

Conclude with `congrArg CommaMorphism.left (lift_snd (a t) (b t))`.
-/
theorem isContFamily_lift {A B : Over (Sp ℂ)} {a : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)} {b : T → (𝟙_ (Over (Sp ℂ)) ⟶ B)}
    (ha : IsContFamily (X := A.left) (fun t => (a t).left)) (hb : IsContFamily (X := B.left) (fun t => (b t).left)) :
    IsContFamily (X := (A ⊗ B).left) (fun t => (lift (a t) (b t)).left) := by
  have H : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback A.hom B.hom
  refine isContFamily_of_isPullback hv H ?_ ?_
  · convert ha using 2 with t
    exact congrArg CommaMorphism.left (lift_fst (a t) (b t))
  · convert hb using 2 with t
    exact congrArg CommaMorphism.left (lift_snd (a t) (b t))

end GlobalTheory.ComplexPointsGroup

namespace GlobalTheory

open ComplexPointsGroup in

/- English proof (translation)
Introduce `hv A _`. Set `: TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ A)` to `TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}`. Establish `hmul : ContinuousMul (𝟙_ (Over (Sp ℂ)) ⟶ A)` using `⟨by`. Use `(continuous_iff_isContFamily _).2 ?_` and prove the remaining obligations. Conclude with `(isContFamily_lift hv ((continuous_iff_isContFamily _).1 continuous_fst) ((continuous_iff_isContFamily _).1 continuous_snd)).comp hv μ[A].left⟩`.

Establish `hinv : ContinuousInv (𝟙_ (Over (Sp ℂ)) ⟶ A)` using `⟨by`. Use `(continuous_iff_isContFamily _).2 ?_` and prove the remaining obligations. Conclude with `((continuous_iff_isContFamily _).1 continuous_id).comp hv (GrpObj.inv (X := A)).left⟩`. Conclude with `{}`.
-/
theorem isTopologicalGroup_complexPoints :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp ℂ)) [GrpObj A], @IsTopologicalGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}) _) := by
  intro hv A _
  let : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
  have hmul : ContinuousMul (𝟙_ (Over (Sp ℂ)) ⟶ A) := ⟨by
    refine (continuous_iff_isContFamily _).2 ?_
    exact (isContFamily_lift hv ((continuous_iff_isContFamily _).1 continuous_fst)
      ((continuous_iff_isContFamily _).1 continuous_snd)).comp hv μ[A].left⟩
  have hinv : ContinuousInv (𝟙_ (Over (Sp ℂ)) ⟶ A) := ⟨by
    refine (continuous_iff_isContFamily _).2 ?_
    exact ((continuous_iff_isContFamily _).1 continuous_id).comp hv (GrpObj.inv (X := A)).left⟩
  exact {}

end GlobalTheory
