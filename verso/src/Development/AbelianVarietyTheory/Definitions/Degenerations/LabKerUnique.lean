import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical

namespace RealModel
open Inh

/- English proof (translation)
The claim follows from `map_one _`.
-/
theorem res_one {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : res h (1 : Γ(X, U)ˣ) = 1 := map_one _
/- English proof (translation)
The claim follows from `map_one _`.
-/
theorem pullU_one {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) : pullU f U (1 : Γ(X, U)ˣ) = 1 := map_one _
/- English proof (translation)
Use `ext`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(X, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
/- English proof (translation)
Substitute `hf` using the available equality. Both sides reduce to the same expression.
-/
theorem res_pullU_id {X : Scheme.{0}} (f : X ⟶ X) (hf : f = 𝟙 X) {U V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ U)
    (u : Γ(X, U)ˣ) : res h (pullU f U u) = res h' u := by
  subst hf; rfl

def oneG {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1⟩
/- English proof (translation)
Introduce `i j`. Rewrite using `[linComb_triv_g, _root_.one_mul]`. Conclude with `(res_one _).trans (res_one _).symm`.
-/
theorem oneG_gen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (oneG φ ε).IsGen := by
  intro i j; rw [linComb_triv_g, _root_.one_mul]; exact (res_one _).trans (res_one _).symm

def oneS {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Sec (LB.LinComb (trivLB X) φ ε) := ⟨fun _ => 1, by
  intro i j; rw [linComb_triv_g, Units.val_one, _root_.one_mul]; exact (map_one _).trans (map_one _).symm⟩
/- English proof (translation)
Apply `top_unique` to reduce the goal to its premises. Introduce `x _`. Conclude with `Set.mem_iInter.2 fun _ => trivial`.
-/
theorem wchart_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → (trivLB X).ι) :
    LB.wchart (trivLB X) φ j = ⊤ := by
  apply top_unique
  intro x _
  exact Set.mem_iInter.2 fun _ => trivial

/- English proof (translation)
Introduce `j j' _ _ _`. Conclude with `((congrArg _ (h j)).trans (res_one _)).trans ((congrArg _ (h' j')).trans (res_one _)).symm`.
-/
theorem corr_of_one {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' _ _ _
  exact ((congrArg _ (h j)).trans (res_one _)).trans ((congrArg _ (h' j')).trans (res_one _)).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun _ => 1⟩, by intro i j have : (LB.div M L).g i j = 1 := by simp only [LB.div, hL, hM] erw [res_one, res_one]; simp; rfl rw [this, _root_.one_mul]; exact (res_one _).trans (res_one _).symm⟩`.
-/
theorem isoOne {X : Scheme.{0}} (L M : LB X) (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) : LBIso L M :=
  ⟨⟨fun _ => 1⟩, by
    intro i j
    have : (LB.div M L).g i j = 1 := by
      simp only [LB.div, hL, hM]
      erw [res_one, res_one]; simp; rfl
    rw [this, _root_.one_mul]; exact (res_one _).trans (res_one _).symm⟩

variable (B : Scheme.{0})

/- English proof (translation)
Use `⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, toUnit_unique _ _, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isoOne _ _ (fun _ _ => rfl) (fun _ _ => linComb_triv_g _ _ _ _)`. Conclude with `isoOne _ _ (fun _ _ => linComb_triv_g _ _ _ _) (fun _ _ => linComb_triv_g _ _ _ _)`.
-/
theorem hypS_zero : HypS (zeroPolAV B).A (zeroPolAV B).L := by
  refine ⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, toUnit_unique _ _, ?_, ?_⟩
  · exact isoOne _ _ (fun _ _ => rfl) (fun _ _ => linComb_triv_g _ _ _ _)
  · exact isoOne _ _ (fun _ _ => linComb_triv_g _ _ _ _) (fun _ _ => linComb_triv_g _ _ _ _)

/- English proof (translation)
Substitute `hW` using the available equality. Use `haveI : IsIso (fst T (zeroPolAV B).A) := by show IsIso (fst T (𝟙_ (Over B)))`. Rewrite using `[← rightUnitor_hom]`. Use `infer_instance`. Use `haveI : IsIso (fst T (zeroPolAV B).A).left := inferInstanceAs (IsIso ((Over.forget B).map (fst T (zeroPolAV B).A)))`.

Establish `h` using `ConcreteCategory.bijective_of_isIso ((fst T (zeroPolAV B).A).left.app ⊤)`. Establish `e : liftFun (zeroPolAV B).A (T` using `T) ⊤ = (fst T (zeroPolAV B).A).left.appTop.hom := by`. Use function extensionality and compare the values at `r`. Simplify using `only [liftFun]`. Establish `: (homOfLE (le_top : (⊤ : (T ⊗ (zeroPolAV B).A).left.Opens) ≤ ⊤)).op = 𝟙 _` using `rfl`.

Rewrite using `[this, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h`.
-/
theorem liftFun_bij (T : Over B) (W : (T ⊗ (zeroPolAV B).A).left.Opens) (hW : W = ⊤) :
    Function.Bijective (liftFun (zeroPolAV B).A (T := T) W) := by
  subst hW
  haveI : IsIso (fst T (zeroPolAV B).A) := by
    show IsIso (fst T (𝟙_ (Over B)))
    rw [← rightUnitor_hom]; infer_instance
  haveI : IsIso (fst T (zeroPolAV B).A).left := inferInstanceAs (IsIso ((Over.forget B).map (fst T (zeroPolAV B).A)))
  have h := ConcreteCategory.bijective_of_isIso ((fst T (zeroPolAV B).A).left.app ⊤)
  have e : liftFun (zeroPolAV B).A (T := T) ⊤ = (fst T (zeroPolAV B).A).left.appTop.hom := by
    funext r
    simp only [liftFun]
    have : (homOfLE (le_top : (⊤ : (T ⊗ (zeroPolAV B).A).left.Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id]; rfl
  rw [e]; exact h

/- English proof (translation)
Establish `: translT (zeroPolAV B).A x = 𝟙 _`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT]`. Conclude with `toUnit_unique _ _`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem translT_id {T : Over B} (x : T ⟶ (zeroPolAV B).A) : (translT (zeroPolAV B).A x).left = 𝟙 _ := by
  have : translT (zeroPolAV B).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

/- English proof (translation)
Substitute `hh hh'` using the available equality. Introduce `j j' _ _ _`. Set `d : K → (trivLB X).ι` to `fun _ => PUnit.unit`. Establish `ha : ⊤ ≤ LB.wchart (trivLB X) φ d` using `by rw [wchart_triv]`. Establish `hb : ⊤ ≤ LB.wchart (trivLB X) φ' d` using `by rw [wchart_triv]`.

Establish `e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ), res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v` using `by intros; rw [map_mul, res_res, res_res]`. Use `(e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (res_one _))).symm` and prove the remaining obligations. Rewrite using `[_root_.mul_one, _root_.mul_comm]`. Use `congrArg₂ (· * ·) ?_ ?_` and prove the remaining obligations.

Conclude with `(res_res _ _ _)`. Conclude with `(res_res _ _ _).symm`.
-/
theorem corr_comm {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb (trivLB X) φ ε)) (b : LB.Gen (LB.LinComb (trivLB X) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb (trivLB X) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr (trivLB X) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  let d : K → (trivLB X).ι := fun _ => PUnit.unit
  have ha : ⊤ ≤ LB.wchart (trivLB X) φ d := by rw [wchart_triv]
  have hb : ⊤ ≤ LB.wchart (trivLB X) φ' d := by rw [wchart_triv]
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, res_res, res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (res_res _ _ _)
  · exact (res_res _ _ _).symm

/- English proof (translation)
Introduce `p`. Use `⟨⊤, trivial, ⟨⟨_, oneG _ _, oneG_gen _ _⟩, ⟨_, oneG _ _, oneG_gen _ _⟩, rfl, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `θx θy _ _`. Establish `hc : unitRes (T` using `T) ⊤ 1 = 1 := map_one _`. Rewrite using `[hc]`.

Conclude with `corr_comm _ _ _ _ _ _ _ (translT_id B _) (translT_id B _) _ (fun j => (congrArg _ (map_one _)).trans (res_one _))`.
-/
theorem weil_zero (k : ℤ) {T : Over B} (x y : T ⟶ (zeroPolAV B).A) :
    WeilIs (zeroPolAV B).A (zeroPolAV B).L k x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, oneG _ _, oneG_gen _ _⟩, ⟨_, oneG _ _, oneG_gen _ _⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm _ _ _ _ _ _ _ (translT_id B _) (translT_id B _) _
    (fun j => (congrArg _ (map_one _)).trans (res_one _))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def sys0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : ThetaSys o Ω where
  g := 0
  N := 81
  r := 3
  N_ge := by norm_num
  r_pos := by norm_num
  ζ := ζ
  prim := hζ
  unit := hu
  J := Unit
  ρ := fun _ => 1
  ρ_one := fun _ _ => Subsingleton.elim _ _ |> fun (_ : () = ()) => by ext i j; simp [Matrix.one_apply]
  ρ_mul := fun _ _ => ⟨0, by simp⟩
  ρ_add := fun _ _ _ => by simp
  th := fun _ => 1
  ev := fun _ _ => 1
  R := R
  fg := fg
  frac := frac
  th_mem := fun _ => R.one_mem
  ev_mem := fun _ _ => R.one_mem
  supp := by simp
  th_ne := ⟨0, one_ne_zero⟩

/- English proof (translation)
The claim follows from `map_one _`.
-/
theorem fn_one {R : Type} [CommRing R] : fn (1 : R) = 1 := map_one _
/- English proof (translation)
Simplify using `only [liftFun, map_one]`.
-/
theorem liftFun_one {T : Over B} (A : Over B) (W : (T ⊗ A).left.Opens) : liftFun A (T := T) W 1 = 1 := by
  simp only [liftFun, map_one]

/- English proof (translation)
Set `d : (LPow (zeroPolAV B).A (zeroPolAV B).L k T).ι` to `fun _ => PUnit.unit`. Establish `hb` using `liftFun_bij B T ((LPow (zeroPolAV B).A (zeroPolAV B).L k T).U d) (wchart_triv _ _)`. Take `⟨c, hc⟩` from `hb.2 (σ.f d)`. Use `⟨fun _ => c, fun j => ?_, fun c' h' => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.sum_unique]`.

Conclude with `hc.symm.trans (_root_.mul_one _).symm`. Use function extensionality and compare the values at `i`. Use `h' d` as an intermediate fact. Rewrite `this` using `[Fintype.sum_unique]`. Rewrite using `[Subsingleton.elim i default]`.

Conclude with `hb.1 (((_root_.mul_one _).symm.trans this.symm).trans hc.symm)`.
-/
theorem basis_zero (T : Over B) (k : ℤ) (J : Type) [Fintype J] [Unique J] (σ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T)) :
    ∃! c : J → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun (zeroPolAV B).A _ (c i) *
      (oneS _ _ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T)).f j := by
  let d : (LPow (zeroPolAV B).A (zeroPolAV B).L k T).ι := fun _ => PUnit.unit
  have hb := liftFun_bij B T ((LPow (zeroPolAV B).A (zeroPolAV B).L k T).U d) (wchart_triv _ _)
  obtain ⟨c, hc⟩ := hb.2 (σ.f d)
  refine ⟨fun _ => c, fun j => ?_, fun c' h' => ?_⟩
  · rw [Fintype.sum_unique]; exact hc.symm.trans (_root_.mul_one _).symm
  · funext i
    have := h' d
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim i default]
    exact hb.1 (((_root_.mul_one _).symm.trans this.symm).trans hc.symm)

/- English proof (translation)
Introduce `j`. Use `((congrArg _ (map_one _)).trans (map_one _)).trans ?_` and prove the remaining obligations. Rewrite using `[map_one, _root_.one_mul]`. Conclude with `(congrArg Units.val (hτ j)).symm`.
-/
theorem value_one (k : ℤ) {T : Over B} (z : T ⟶ (zeroPolAV B).A)
    (τ : LB.Gen (LB.LinComb (zeroPolAV B).L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => k))) (hτ : ∀ j, τ.s j = 1) :
    IsValueAt (zeroPolAV B).A (zeroPolAV B).L k (oneS _ _) z τ 1 := by
  intro j
  refine ((congrArg _ (map_one _)).trans (map_one _)).trans ?_
  rw [map_one, _root_.one_mul]
  exact (congrArg Units.val (hτ j)).symm

/- English proof (translation)
The claim follows from `(congrArg₂ (· * ·) ((congrArg _ (h _)).trans (res_one _)) ((congrArg _ (h' _)).trans (res_one _))).trans (_root_.one_mul _)`.
-/
theorem mul_s_one {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) (j) : (LB.mulGen L φ ε φ' ε' t t').s j = 1 :=
  (congrArg₂ (· * ·) ((congrArg _ (h _)).trans (res_one _)) ((congrArg _ (h' _)).trans (res_one _))).trans (_root_.one_mul _)
/- English proof (translation)
The claim follows from `(congrArg _ ((congrArg _ (h _)).trans (pullU_one _ _))).trans (res_one _)`.
-/
theorem pull_s_one {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (h : ∀ j, t.s j = 1) (j) : (LB.pullGen L φ ε t f).s j = 1 :=
  (congrArg _ ((congrArg _ (h _)).trans (pullU_one _ _))).trans (res_one _)
/- English proof (translation)
The claim follows from `(congrArg (·⁻¹) (h j)).trans inv_one`.
-/
theorem inv_s_one {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : ∀ j, t.s j = 1) (j) : (LB.invGen L φ ε t).s j = 1 :=
  (congrArg (·⁻¹) (h j)).trans inv_one
/- English proof (translation)
The claim follows from `(congrArg (· ^ k) ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (one_zpow _)`.
-/
theorem rigT_one (T : Over B) (k : ℤ) (j) : (rigT (zeroPolAV B).A (zeroPolAV B).L (oneG _ _) T k).s j = 1 :=
  (congrArg (· ^ k) ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (one_zpow _)

/- English proof (translation)
Use `⟨toUnit_unique _ _, oneG_gen _ _, oneG _ _, oneG_gen _ _, ?_, ?_⟩` and prove the remaining obligations. Conclude with `corr_of_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) (mul_s_one _ _ _ _ _ _ _ (fun _ => one_zpow _) (inv_s_one _ _ _ _ fun _ => rfl))`. Conclude with `corr_of_one _ _ _ _ _ _ _ (fun _ => one_zpow _) (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) (rigT_one B _ _))`.
-/
theorem tors_zero (n : ℕ) {T : Over B} (x : T ⟶ (zeroPolAV B).A) :
    IsTorsFrame (zeroPolAV B) (oneG _ _) n x (oneG _ _) := by
  refine ⟨toUnit_unique _ _, oneG_gen _ _, oneG _ _, oneG_gen _ _, ?_, ?_⟩
  · exact corr_of_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
      (mul_s_one _ _ _ _ _ _ _ (fun _ => one_zpow _) (inv_s_one _ _ _ _ fun _ => rfl))
  · exact corr_of_one _ _ _ _ _ _ _ (fun _ => one_zpow _)
      (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) (rigT_one B _ _))

/- English proof (translation)
Use `⟨rfl, corr_of_one _ _ _ _ _ _ _ (fun j => ?_) (fun _ => rfl), oneG _ _, oneG_gen _ _, corr_of_one _ _ _ _ _ _ _ ?_ (fun _ => rfl)⟩` and prove the remaining obligations. Use `show (∏ j₀ : Fin n, (_ : Γ((T ⊗ (zeroPolAV B).A).left, LB.wchart (zeroPolAV B).L (powφ (zeroPolAV B).A x n) j)ˣ)) = 1`. Use `Finset.prod_eq_one fun j₀ _ => ?_` and prove the remaining obligations. Conclude with `(congrArg _ ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (res_one _)`. Conclude with `mul_s_one _ _ _ _ _ _ _ (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) fun _ => rfl) (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) (inv_s_one _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)))`.
-/
theorem symLift_zero (k : ℤ) (n : ℕ) {T : Over B} (x : T ⟶ (zeroPolAV B).A) :
    SymLift (zeroPolAV B).A (zeroPolAV B).L k n x ⟨x, oneG _ _, oneG_gen _ _⟩ := by
  refine ⟨rfl, corr_of_one _ _ _ _ _ _ _ (fun j => ?_) (fun _ => rfl), oneG _ _, oneG_gen _ _,
    corr_of_one _ _ _ _ _ _ _ ?_ (fun _ => rfl)⟩
  · show (∏ j₀ : Fin n, (_ : Γ((T ⊗ (zeroPolAV B).A).left, LB.wchart (zeroPolAV B).L (powφ (zeroPolAV B).A x n) j)ˣ)) = 1
    refine Finset.prod_eq_one fun j₀ _ => ?_
    exact (congrArg _ ((congrArg _ (pullU_one _ _)).trans (res_one _))).trans (res_one _)
  · exact mul_s_one _ _ _ _ _ _ _ (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl) fun _ => rfl)
      (mul_s_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
        (inv_s_one _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)))

/- English proof (translation)
Introduce `j`. Use `(map_one _).trans ?_` and prove the remaining obligations. Conclude with `((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _)).symm`.
-/
theorem twist_one {T : Over B} (ψ : T ⊗ (zeroPolAV B).A ⟶ T ⊗ (zeroPolAV B).A) (m) (hm : ψ ≫ snd T _ = m) (a b : ℤ) :
    IsTwistPull (zeroPolAV B).A (zeroPolAV B).L ψ m hm a b (oneG _ _) (oneS _ _) (oneS _ _) := by
  intro j
  refine (map_one _).trans ?_
  exact ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _)).symm

/- English proof (translation)
Establish `h1` using `(h (fun _ => PUnit.unit)).trans ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _))`. Establish `key : ∀ (Y : Scheme.{0}) (U V : Y.Opens) (hle : V ≤ U) (_ : U = ⊤) (_ : V = ⊤) (f : Γ(Y, U)), (Y.presheaf.map (homOfLE hle).op).hom f = 1 → f = 1`. Introduce `Y U V hle hU hV f hf`. Substitute `hU hV` using the available equality. Establish `: (homOfLE hle).op = 𝟙 _` using `rfl`.

Rewrite `hf` using `[this, CategoryTheory.Functor.map_id]`. Conclude with `hf`. Conclude with `key _ _ _ _ (wchart_triv _ _) (wchart_triv _ _) _ h1`.
-/
theorem act_one {T : Over B} (x : T ⟶ (zeroPolAV B).A) (k : ℤ) (σ : LB.Sec (LPow (zeroPolAV B).A (zeroPolAV B).L k T))
    (h : IsActOf (zeroPolAV B).A (zeroPolAV B).L k ⟨x, oneG _ _, oneG_gen _ _⟩ (oneS _ _) σ) (j) : σ.f j = 1 := by
  have h1 := (h (fun _ => PUnit.unit)).trans
    ((congrArg₂ (· * ·) rfl ((congrArg _ (map_one _)).trans (map_one _))).trans (_root_.one_mul _))
  have key : ∀ (Y : Scheme.{0}) (U V : Y.Opens) (hle : V ≤ U) (_ : U = ⊤) (_ : V = ⊤) (f : Γ(Y, U)),
      (Y.presheaf.map (homOfLE hle).op).hom f = 1 → f = 1 := by
    intro Y U V hle hU hV f hf
    subst hU hV
    have : (homOfLE hle).op = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id] at hf
    exact hf
  exact key _ _ _ _ (wchart_triv _ _) (wchart_triv _ _) _ h1

def real0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : (sys0 ζ hζ hu R fg frac).Real where
  P := zeroPolAV _
  g_eq := rfl
  hypS := hypS_zero _
  n := 3
  n_prime := Nat.prime_three
  n_odd := by decide
  k := 2
  two_le := le_rfl
  N_eq := rfl
  r_eq := ⟨1, le_rfl, rfl⟩
  card := rfl
  pt := fun _ => 1
  pt_add := fun _ _ => (_root_.mul_one _).symm
  pt_bij := fun K _ _ x z _ => ⟨0, toUnit_unique _ _, fun a _ => funext fun i => by
    rcases i with i | i <;> exact i.elim0⟩
  weil := fun a b c hc => by
    have h0 : eStd (sys0 ζ hζ hu R fg frac).g _ a b = 0 := Finset.sum_eq_zero fun i _ => i.elim0
    rw [h0, ZMod.val_zero, Nat.mul_zero, pow_zero, map_one] at hc
    have : c = 1 := Units.ext hc
    subst this
    have : unitOn (1 : ((sys0 ζ hζ hu R fg frac).R)ˣ) = 1 := map_one _
    rw [this]
    exact weil_zero _ _ _ _
  rig := oneG _ _
  rig_gen := oneG_gen _ _
  th₁ := oneS _ _
  th₁_basis := fun σ => basis_zero _ _ _ (Fin 1) σ
  fr := fun _ => oneG _ _
  fr_tors := fun _ => tors_zero _ _ _
  th_val := fun _ => by
    refine (congrArg _ fn_one).mpr ?_
    exact value_one _ _ _ _ fun _ => rfl
  s := fun _ => oneS _ _
  s_basis := fun σ => basis_zero _ _ _ Unit σ
  ev_val := fun _ _ => by
    refine (congrArg _ fn_one).mpr ?_
    exact value_one _ _ _ _ fun _ => one_zpow _
  i₀ := ()
  α := oneG _ _
  α_gen := oneG_gen _ _
  α_norm := corr_of_one _ _ _ _ _ _ _ (pull_s_one _ _ _ _ _ fun _ => rfl)
    (mul_s_one _ _ _ _ _ _ _ (rigT_one _ _ _) (rigT_one _ _ _))
  s_zero := twist_one _ _ _ _ _ _
  U := fun _ => ⟨1, oneG _ _, oneG_gen _ _⟩
  U_sym := fun _ => symLift_zero _ _ _ _
  U_act := fun a i σ h j => by
    refine (act_one _ _ _ σ h j).trans ?_
    have : ∀ l : Unit, (1 : Matrix Unit Unit o) l i = 1 := fun l => Matrix.one_apply_eq _
    refine Eq.symm ((Finset.sum_eq_single_of_mem () (Finset.mem_univ _) (fun _ _ h => absurd rfl h)).trans ?_)
    refine (_root_.mul_one _).trans ?_
    refine (congrArg _ ((congrArg fn ((congrArg _ (this _)).trans (map_one _))).trans fn_one)).trans (liftFun_one _ _ _)
  orbit := fun i => ⟨0, 0, fun l => by
    refine Eq.trans ?_ ((if_pos rfl).trans (pow_zero _)).symm
    exact @Matrix.one_apply_eq Unit o instDecidableEqPUnit _ _ ()⟩

/- English proof (translation)
Simplify using `[ThetaSys.Big, sys0]`.
-/
theorem big0 (ζ : o) (hζ : IsPrimitiveRoot ζ ((3 * 81) ^ 2)) (hu : IsUnit ((3 * 81 : ℕ) : o)) (R : Subalgebra o Ω)
    (fg : R.FG) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) : (sys0 ζ hζ hu R fg frac).Big := by
  simp [ThetaSys.Big, sys0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨sys0 _ (Complex.isPrimitiveRoot_exp _ (by norm_num)) (by simp) ⊤ (Algebra.FiniteType.out : (⊤ : Subalgebra ℂ ℂ).FG) (fun x => ⟨x, trivial, 1, trivial, by simp⟩), ⟨real0 _ _ _ _ _ _⟩, big0 _ _ _ _ _ _⟩`.
-/
theorem exists_real : ∃ S : ThetaSys ℂ ℂ, Nonempty S.Real ∧ S.Big :=
  ⟨sys0 _ (Complex.isPrimitiveRoot_exp _ (by norm_num)) (by simp) ⊤ (Algebra.FiniteType.out : (⊤ : Subalgebra ℂ ℂ).FG)
    (fun x => ⟨x, trivial, 1, trivial, by simp⟩), ⟨real0 _ _ _ _ _ _⟩, big0 _ _ _ _ _ _⟩

/- English proof (translation)
The claim follows from `τ.δ_max.csSup_eq`.
-/
theorem delta_eq (S : ThetaSys o Ω) {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y) :
    S.delta y = τ.δ := τ.δ_max.csSup_eq

/- English proof (translation)
Establish `hc` using `u.D.toPre.P.isLB.cover`. Set `x : Sp u.V` to `IsLocalRing.closedPoint u.V`. Establish `hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i` using `by rw [hc]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Establish `htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i` using `((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge`.

Conclude with `(h (fun _ => i) htop).symm.trans (h' (fun _ => i) htop)`.
-/
theorem psiNorm_unique {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (χ : u.D.toPre.X) {r r' : ℝ} (h : u.PsiNorm χ r) (h' : u.PsiNorm χ r') : r = r' := by
  have hc := u.D.toPre.P.isLB.cover
  let x : Sp u.V := IsLocalRing.closedPoint u.V
  have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
    ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
  exact (h (fun _ => i) htop).symm.trans (h' (fun _ => i) htop)

section More
variable {S : ThetaSys o Ω} (ρ : S.Real)

/- English proof (translation)
Establish `h` using `ρ.pt_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.1 h.symm`.
-/
theorem pt_zero : ρ.pt 0 = 1 := by
  have h := ρ.pt_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, pt_zero]`. Consider the case `succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]`.
-/
theorem pt_nsmul (a : S.Gam) (n : ℕ) : ρ.pt (n • a) = ρ.pt a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, pt_zero]
  | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

/- English proof (translation)
Introduce `a b hab`. Set `x : Sp (AlgebraicClosure Ω) ⟶ Sp S.R` to `spMap ((algebraMap Ω (AlgebraicClosure Ω)).comp S.R.val.toRingHom)`. Establish `ht : ρ.pt a ^ (S.r * S.N) = 1` using `(ρ.fr_tors a).1`. Take `⟨c, -, hc⟩` from `ρ.pt_bij (AlgebraicClosure Ω) x ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp S.R)) ≫ ρ.pt a) (by rw [← MonObj.comp_pow, ht, MonObj.comp_one])`. Conclude with `(hc a rfl).trans (hc b (by rw [hab])).symm`.
-/
theorem pt_injective : Function.Injective ρ.pt := by
  intro a b hab
  let x : Sp (AlgebraicClosure Ω) ⟶ Sp S.R := spMap ((algebraMap Ω (AlgebraicClosure Ω)).comp S.R.val.toRingHom)
  have ht : ρ.pt a ^ (S.r * S.N) = 1 := (ρ.fr_tors a).1
  obtain ⟨c, -, hc⟩ := ρ.pt_bij (AlgebraicClosure Ω) x
    ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp S.R)) ≫ ρ.pt a)
    (by rw [← MonObj.comp_pow, ht, MonObj.comp_one])
  exact (hc a rfl).trans (hc b (by rw [hab])).symm

/- English proof (translation)
Use `⟨ρ.N_eq ▸ (ρ.n_odd.pow).pow, ?_⟩` and prove the remaining obligations. Establish `h3 : 3 ≤ ρ.n`. Use `ρ.n_prime.two_le` as an intermediate fact. Take `⟨t, ht⟩` from `ρ.n_odd`. Use linear arithmetic over natural numbers and integers.

Establish `h9 : 9 ≤ ρ.n ^ ρ.k` using `le_trans (Nat.pow_le_pow_left h3 2) (Nat.pow_le_pow_right (by omega) ρ.two_le)`. Rewrite using `[ρ.N_eq]`. Conclude with `Nat.pow_le_pow_left h9 2`.
-/
theorem N_odd (ρ : S.Real) : Odd S.N ∧ 81 ≤ S.N := by
  refine ⟨ρ.N_eq ▸ (ρ.n_odd.pow).pow, ?_⟩
  have h3 : 3 ≤ ρ.n := by
    have := ρ.n_prime.two_le
    obtain ⟨t, ht⟩ := ρ.n_odd
    omega
  have h9 : 9 ≤ ρ.n ^ ρ.k :=
    le_trans (Nat.pow_le_pow_left h3 2) (Nat.pow_le_pow_right (by omega) ρ.two_le)
  rw [ρ.N_eq]; exact Nat.pow_le_pow_left h9 2
variable {ρ} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

/- English proof (translation)
Use extensionality with `χ`. Use `psiNorm_unique u χ (l.q_eq χ) (l'.q_eq χ)` as an intermediate fact. Conclude with `neg_injective (Real.exp_injective this)`.
-/
theorem lab_q_unique (l l' : u.Lab) : l.q = l'.q := by
  ext χ
  have := psiNorm_unique u χ (l.q_eq χ) (l'.q_eq χ)
  exact neg_injective (Real.exp_injective this)

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[l.ker_iff, l'.ker_iff]`.
-/
theorem lab_ker_unique (l l' : u.Lab) : l.yy.ker = l'.yy.ker := by
  ext a; rw [l.ker_iff, l'.ker_iff]

/- English proof (translation)
Take `⟨x, hx⟩` from `l.yy_onto (QuotientAddGroup.mk α)`. Conclude with `⟨x, l.wt_eq x α hx⟩`.
-/
theorem lab_wt_eq (l : u.Lab) (α : u.D.toPre.X) : ∃ x : S.Gam, ∀ t : S.perp l.yy.ker,
    l.wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  obtain ⟨x, hx⟩ := l.yy_onto (QuotientAddGroup.mk α)
  exact ⟨x, l.wt_eq x α hx⟩
end More

/- English proof (translation)
Establish `h1 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)`. Establish `h3 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - 1)`. Combine the equalities or inequalities in the displayed calculation.

Prove the components needed by the constructor for the conclusion. Introduce `hr`. Simplify using `only [ThetaSys.Big, hg, hN, hr]`. Apply the tactic sequence `refine ⟨?_, ?_, by norm_num⟩ <;> push_cast <;> nlinarith`. Introduce `hr h`.

Simplify using `only [ThetaSys.Big, hg, hN, hr] at h`. Use `h.2.1` as an intermediate fact. Move the coercions through the operations in `at this`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem big_one (S : ThetaSys o Ω) (hg : S.g = 1) (hN : S.N = 81) :
    (S.r = 243 → S.Big) ∧ (S.r = 81 → ¬ S.Big) := by
  have h1 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h3 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) := by
    calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  constructor
  · intro hr
    simp only [ThetaSys.Big, hg, hN, hr]
    refine ⟨?_, ?_, by norm_num⟩ <;> push_cast <;> nlinarith
  · intro hr h
    simp only [ThetaSys.Big, hg, hN, hr] at h
    have := h.2.1
    push_cast at this
    nlinarith

end RealModel
end GlobalTheory.ZH
end
