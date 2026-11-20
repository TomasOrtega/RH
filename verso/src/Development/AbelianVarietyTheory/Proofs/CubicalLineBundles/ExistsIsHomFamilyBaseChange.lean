import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in

/- English proof (translation)
Use `⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w φ, hβ]`. Conclude with `hπ.lift_fst _ _ _`.
-/
theorem _root_.GlobalTheory.PureType.exists_hom_over (hβ : β ≫ B.hom = B'.hom ≫ f)
    (hπ : IsPullback π G'.hom G.hom f) (φ : B ⟶ G) :
    ∃ φ' : B' ⟶ G', φ'.left ≫ π = β ≫ φ.left := by
  refine ⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Over.w φ, hβ]
  · exact hπ.lift_fst _ _ _

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (hπ.hom_ext h (by simp))`.
-/
theorem _root_.GlobalTheory.PureType.eq_of_comp_eq (hπ : IsPullback π G'.hom G.hom f) {T : Over S'}
    {x y : T ⟶ G'} (h : x.left ≫ π = y.left ≫ π) : x = y :=
  Over.OverMorphism.ext (hπ.hom_ext h (by simp))

variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G']

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G'] in

/- English proof (translation)
Establish `key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ')`. Introduce `T x y`. Establish `hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom`. Introduce `z`. Rewrite using `[Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]`.

Both sides reduce to the same expression. Set `x₀ : Over.mk (T.hom ≫ f) ⟶ B` to `Over.homMk (x.left ≫ β) (hw x)`. Set `y₀ : Over.mk (T.hom ≫ f) ⟶ B` to `Over.homMk (y.left ≫ β) (hw y)`. Establish `h₁` using `hβ.2 T x y x₀ y₀ rfl rfl`. Establish `h₂` using `hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])`.

Apply `_root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1` to reduce the goal to its premises. Rewrite using `[← h₂, ← MonObj.mul_comp]`. Simplify using `only [Over.comp_left, h₁, Category.assoc, h]`. Establish `one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1`. Introduce `T`.

Use `key T 1 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)`. Prove the components needed by the constructor for the conclusion. Simplify `one (𝟙_ _)` using `[Hom.one_def]`.

Use `key (B' ⊗ B') (fst B' B') (snd B' B')` as an intermediate fact. Simplify `this` using `[Hom.mul_def]`.
-/
theorem _root_.GlobalTheory.PureType.isMonHom_over (hβ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback B' B f β) (hπ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f π) {φ : B ⟶ G}
    [IsMonHom φ] {φ' : B' ⟶ G'} (h : φ'.left ≫ π = β ≫ φ.left) : IsMonHom φ' := by
  have key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ') := by
    intro T x y
    have hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
      intro z
      rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]
      rfl
    let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (x.left ≫ β) (hw x)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (y.left ≫ β) (hw y)
    have h₁ := hβ.2 T x y x₀ y₀ rfl rfl
    have h₂ := hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])
    apply _root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1
    rw [← h₂, ← MonObj.mul_comp]
    simp only [Over.comp_left, h₁, Category.assoc, h]
  have one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1 := by
    intro T
    have := key T 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)
  constructor
  · simpa [Hom.one_def] using one (𝟙_ _)
  · have := key (B' ⊗ B') (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

omit [GrpObj B] [GrpObj B'] in

/- English proof (translation)
Set `U : Over.mk (B'.hom ≫ f) ⟶ B` to `Over.homMk β hβ`. Rewrite using `[← hπ.2 B' _ _ (U ≫ φ₁) (U ≫ φ₂) h₁.symm h₂.symm, ← MonObj.comp_mul]`. Both sides reduce to the same expression.
-/
theorem mul_over (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π) {φ₁ φ₂ : B ⟶ G} {φ₁' φ₂' : B' ⟶ G'}
    (h₁ : φ₁'.left ≫ π = β ≫ φ₁.left) (h₂ : φ₂'.left ≫ π = β ≫ φ₂.left) :
    (φ₁' * φ₂').left ≫ π = β ≫ (φ₁ * φ₂).left := by
  let U : Over.mk (B'.hom ≫ f) ⟶ B := Over.homMk β hβ
  rw [← hπ.2 B' _ _ (U ≫ φ₁) (U ≫ φ₂) h₁.symm h₂.symm, ← MonObj.comp_mul]
  rfl

end Grp

/- English proof (translation)
Take `⟨w, hw⟩` from `eP`. Establish `e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π))` using `iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)`. Establish `e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β)` using `LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))`. Establish `e₃` using `LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂`. Use `LBIso.trans (isLB_lbPow (pull_isLB hP' _) _) (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow hM' _) (lbIso_lbPow e₃ n) ?_` and prove the remaining obligations.

Conclude with `LBIso.trans (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow (pull_isLB hM _) _) (isLB_lbPow hM' _) (LBIso.chartPull (chartPullPowPull _ β _) (chartPullPowPull M β _) hI) (lbIso_lbPow eM.symm _)`.
-/
theorem lbIso_pow_over {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n n' : ℕ}
    (hI : LBIso (lbPow (P.pull φ) n) (lbPow M n')) : LBIso (lbPow (P'.pull φ') n) (lbPow M' n') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow (pull_isLB hP' _) _) (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _)
    (isLB_lbPow hM' _) (lbIso_lbPow e₃ n) ?_
  exact LBIso.trans (isLB_lbPow (pull_isLB (pull_isLB hP _) _) _) (isLB_lbPow (pull_isLB hM _) _) (isLB_lbPow hM' _)
    (LBIso.chartPull (chartPullPowPull _ β _) (chartPullPowPull M β _) hI) (lbIso_lbPow eM.symm _)

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨h₁, h₂, h₃, h₄, h₅⟩` from `h`. Establish `hact : ∀ s a, (φ' a ≫ t'.act.act s).left ≫ m.φ = β ≫ (φ a ≫ t.act.act s).left` using `fun s a => by`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc]`. Use `⟨fun a => have := h₁ a; isMonHom_over hβ m.cart (hφ a), fun a b => eq_of_comp_eq m.cart.1 ?_, fun s a => eq_of_comp_eq m.cart.1 ?_, fun a => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_over hβ.1.w m.cart (hφ a) (hφ b), ← h₂]`.

Conclude with `hφ _`. Rewrite using `[hact, ← h₃]`. Conclude with `hφ _`. Establish `e` using `(LieMultiple.isLieComb_one_iff _ _ _).1 (h₄ a)`. Rewrite using `[LieMultiple.isLieComb_one_iff_comp]`.

Use `eq_of_comp_eq m.cart.1 ?_` and prove the remaining obligations. Use `show (v'.left ≫ (φ' a ≫ t'.act.act H.rt).left) ≫ m.φ = (spMap (epsScaleR (f ρ)) ≫ v'.left ≫ (φ' a).left) ≫ m.φ`. Rewrite using `[Category.assoc, hact, Category.assoc, Category.assoc, hφ, ← Category.assoc, ← Category.assoc v'.left, hv, Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _), spMap_spMap, spMap_spMap]`. Use `congr 2`. Apply the tactic sequence `ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`.

Take `⟨N, hN, hI⟩` from `h₅ a ha`. Take `⟨w, g, -⟩` from `m.lin`. Conclude with `⟨N, hN, lbIso_pow_over (hφ a) t.PP.isLB t'.PP.isLB hM hM' ⟨w, g⟩ eM hI⟩`.
-/
theorem IsHomFamily.baseChange {D : Datum H} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'}
    {t : SAB H (Sp R)} {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f))
    {B : Over (Sp R)} {B' : Over (Sp R')} [GrpObj B] [GrpObj B'] {β : B'.left ⟶ B.left}
    (hβ : IsGrpPullback B' B (spMap f) β) {M : LB B.left} {M' : LB B'.left} (hM : M.IsLB) (hM' : M'.IsLB)
    (eM : LBIso M' (M.pull β)) {v : epsR R ⟶ B} {v' : epsR R' ⟶ B'}
    (hv : v'.left ≫ β = spMap (Chart.dualMapR f) ≫ v.left) {L : Submodule (𝓞 E) D.La} {ρ : R} {S : Set L}
    {φ : L → (B ⟶ t.G)} {φ' : L → (B' ⟶ t'.G)} (hφ : ∀ a, (φ' a).left ≫ m.φ = β ≫ (φ a).left)
    (h : IsHomFamily t B M v L ρ S φ) : IsHomFamily t' B' M' v' L (f ρ) S φ' := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have hact : ∀ s a, (φ' a ≫ t'.act.act s).left ≫ m.φ = β ≫ (φ a ≫ t.act.act s).left := fun s a => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc]
  refine ⟨fun a => have := h₁ a; isMonHom_over hβ m.cart (hφ a), fun a b => eq_of_comp_eq m.cart.1 ?_,
    fun s a => eq_of_comp_eq m.cart.1 ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [mul_over hβ.1.w m.cart (hφ a) (hφ b), ← h₂]
    exact hφ _
  · rw [hact, ← h₃]
    exact hφ _
  · have e := (LieMultiple.isLieComb_one_iff _ _ _).1 (h₄ a)
    rw [LieMultiple.isLieComb_one_iff_comp]
    refine eq_of_comp_eq m.cart.1 ?_
    show (v'.left ≫ (φ' a ≫ t'.act.act H.rt).left) ≫ m.φ = (spMap (epsScaleR (f ρ)) ≫ v'.left ≫ (φ' a).left) ≫ m.φ
    rw [Category.assoc, hact, Category.assoc, Category.assoc, hφ, ← Category.assoc, ← Category.assoc v'.left, hv,
      Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
      spMap_spMap, spMap_spMap]
    congr 2
    ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · obtain ⟨N, hN, hI⟩ := h₅ a ha
    obtain ⟨w, g, -⟩ := m.lin
    exact ⟨N, hN, lbIso_pow_over (hφ a) t.PP.isLB t'.PP.isLB hM hM' ⟨w, g⟩ eM hI⟩

end PureType

end GlobalTheory
