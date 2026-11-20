import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumRigidZero

/- English proof (translation)
Introduce `S S' B B' _ _ _ _ M M' hM hM' hB f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `hL : (abelian₂ B M).IsLB` using `DVR.linComb_isLB _ hM _ _`. Establish `hL' : (abelian₂ B' M').IsLB` using `DVR.linComb_isLB _ hM' _ _`. Establish `hw₀ : β ≫ B.hom = B'.hom ≫ f` using `hβ.1.w`.

Establish `pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b` using `fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm`. Establish `pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1` using `fun T₀ => mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (_root_.mul_one 1)))`. Establish `β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left` using `fun a b => square_over_hom_ext (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl) (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)`. Establish `Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U), ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i = h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ * h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).lef …` using `fun a b U _ h => by`. Rewrite using `[β₂_lift]`.

Conclude with `prod_lam (toBase hw₀ a) (toBase hw₀ b) h`. Set `φ1 : Fin 1 → (B'.left ⟶ (G2 B').left)` to `fun _ => (lift (𝟙 B') (1 : B' ⟶ B')).left`. Set `ε1 : Fin 1 → ℤ` to `fun _ => 1`. Establish `fe' : FormEq (K` using `PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by`. Rewrite using `[prod_flat, Fin.prod_univ_one, Fintype.prod_empty]`.

Use `show 1 = (∏ i, h ((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)`. Rewrite using `[prod_lam, _root_.mul_one (𝟙 B')]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]`. Normalize the expressions using the abelian group laws.

Establish `fe : FormEq (K` using `PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) := fun U _ h => by`. Rewrite using `[prod_flat, Fin.prod_univ_one, Fintype.prod_empty]`. Use `show 1 = (∏ i, h (((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)`. Rewrite using `[Hlam, pt_one, _root_.mul_one (toBase hw₀ (𝟙 B'))]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]`. Normalize the expressions using the abelian group laws. Take `⟨g', hg', hv'⟩` from `exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)`. Take `⟨g, hg, hv⟩` from `exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)`. Establish `Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ → val (L` using `abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by`.

Use `(val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_` and prove the remaining obligations. Simplify using `only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]`. Conclude with `(hv' _ r z₀ J₀ hJ₀).trans (val_one r)`. Establish `Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ → val (L` using `abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 := fun r z₀ J₀ hJ₀ => by`. Use `(val_nest hg r (good_ind hJ₀) hJ₀).trans ?_` and prove the remaining obligations.

Simplify using `only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]`. Conclude with `(hv _ r z₀ J₀ hJ₀).trans (val_one r)`. Establish `Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι) (J₀' : (T₀.left ⟶ B'.left) → M'.ι), pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) = lamVal w (lift c (1 : T₀ ⟶ B')).left z₀ J₀ J₀'`. Introduce `T₀ c z₀ J₀ J₀'`. Rewrite using `[pw_eq, Fin.prod_univ_one]`.

Use `show lamVal w (c ≫ lift (𝟙 B') (1 : B' ⟶ B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _`. Rewrite using `[comp_lift, comp_one_pt, Category.comp_id, zpow_one]`. Establish `he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _` using `Over.w (1 : 𝟙_ (Over S') ⟶ B')`. Establish `E` using `rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB).2 (fun y₀ => by`. Take `⟨J₁, hJ₁⟩` from `GlobalTheory.UU.exists_good_pt hM y₀`.

Take `⟨J₁', hJ₁'⟩` from `GlobalTheory.UU.exists_good_pt hM' y₀`. Use `⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩` and prove the remaining obligations. Rewrite using `[Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁', _root_.mul_one])`. Use the proof step `T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')`. Rewrite `E` using `[Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one]`.

Conclude with `E.symm`.
-/
theorem lamVal_one_right_base : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift y (1 : T ⟶ B')).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (_root_.mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (𝟙 B') (1 : B' ⟶ B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.mul_one (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.mul_one (toBase hw₀ (𝟙 B'))]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift c (1 : T₀ ⟶ B')).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (𝟙 B') (1 : B' ⟶ B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
