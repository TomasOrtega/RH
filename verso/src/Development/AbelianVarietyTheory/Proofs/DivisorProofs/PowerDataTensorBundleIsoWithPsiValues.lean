import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoOfJoinGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

/- English proof (translation)
Introduce `R _ _ D D₀ r W pr j h k h1 h2 h3 h4 h5 h6`. Take `⟨u, hu, hu'⟩` from `h6`. Take `⟨κ, hκ, hκ'⟩` from `h5`. Use `choose Γ hΓ hΓ' using h4`. Establish `hp₁` using `isPart_inl D.P.L D₀.P.L`.

Set `g : Fin r → (D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left)` to `fun b => (lift (𝟙 D.P.A) (pr b)).left`. Set `Φ : Fin r → Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ D.P.A.left ⨿ D₀.P.A.left)` to `fun a => Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) k ≫ coprod.inl) (fun k => lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) k ≫ coprod.inr)`. Set `P` to `prodZGen (JN D D₀) (fun ab : Fin r × Fin r => fun m => g ab.2 ≫ Φ ab.1 m) (fun _ => Sum.elim Oε Oinvε) (fun ab => -W ab.1 ab.2) (fun ab => LB.pullGen (JN D D₀) _ _ (Γ ab.1) (g ab.2))`. Establish `hP : P.IsGen` using `prodZGen_isGen (jn_isLB D D₀) _ fun ab => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (hΓ ab.1) _`. Set `rig0` to `LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (toUnit D.P.A).left`.

Establish `hrig0 : rig0.IsGen` using `ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _`. Set `T0` to `LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (hp₁.gen u) (LB.invGen (JN D D₀) _ _ (hp₁.gen κ))) P) (LB.invGen (JN D D₀) _ _ (hp₁.gen rig0))`. Establish `hT0 : T0.IsGen`. Use `ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hp₁.gen_isGen hu) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen …` and prove the remaining obligations. Take `⟨t, ht, htv⟩` from `exists_gen (jn_isLB D D₀) (φ' := Sum.elim (fun k => tensφ pr k ≫ coprod.inr) (fun _ : PUnit => 𝟙 D.P.A.left ≫ coprod.inl)) (ε' := Sum.elim (tensε W) (fun _ => -1)) (by`.

Introduce `U _ hh`. Use `clear hu' hκ' hΓ' h3 h1 h2 hT0 hP hrig0`. Establish `cl : ∀ {T T' : Over (Sp R)} {B : Over (Sp R)} [GrpObj B] (s : T' ⟶ T) (x y : T ⟶ B) (i : Fin 4), s.left ≫ lamPts x y i = lamPts (s ≫ x) (s ≫ y) i`. Introduce `T T' B _ s x y i`. Use `fin_cases i`.

Conclude with `congrArg (fun q => q.left) (MonObj.comp_mul s x y)`. Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one s)`. Establish `hD1 : ∀ a b i, g b ≫ Φ a (Sum.inl i) = lamPts (𝟙 D.P.A) (pr b ≫ j a) i ≫ coprod.inl`.

Introduce `a b i`. Use `show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) i ≫ coprod.inl = _`. Rewrite using `[← Category.assoc, cl, lift_fst, lift_snd_assoc]`. Establish `hD2 : ∀ a b i, g b ≫ Φ a (Sum.inr i) = tensφ pr ((a, b), i) ≫ coprod.inr`. Introduce `a b i`.

Use `show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) i ≫ coprod.inr = _`. Rewrite using `[← Category.assoc, cl, lift_fst_assoc, lift_snd, Category.id_comp]`. Both sides reduce to the same expression. Apply the tactic sequence `have hOi : ∀ i, Oinvε i = - Oε i := by intro i; fin_cases i <;> rfl`. Establish `hCD : (∏ p : (Fin r × Fin r) × Fin 4, hh (lamPts (𝟙 D.P.A) (pr p.1.2 ≫ j p.1.1) p.2 ≫ coprod.inl) ^ (- -(W p.1.1 p.1.2 * Oε p.2))) * (∏ p : (Fin r × Fin r) × (Fin 4 ⊕ Fin 4), hh (g p.1.2 ≫ Φ p.1.1 p.2) ^ (-W p.1.1 p.1.2 * Sum.elim Oε Oinvε p.2)) = ∏ p : (Fin r × Fin r) × Fin 4, h …`.

Rewrite using `[Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun ab _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_sum_type, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hD1, hD2, Sum.elim_inl, Sum.elim_inr, hOi]`.

Simplify using `only [tensε, neg_neg, neg_mul, mul_neg, zpow_neg, mul_inv_cancel, _root_.one_mul, Prod.mk.eta]`. Establish `hAB : (∏ i : Fin 4, hh (![(padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)).left, 𝟙 D.P.A.left, (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2).left, (toUnit D.P.A ≫ η[D.P.A]).left] i ≫ coprod.inl) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) i)) * (∏ i …`. Simplify using `only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]`. Establish `e0 : (𝟙 D.P.A * ∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) = padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)` using `rfl`. Establish `e1 : (1 : D.P.A ⟶ D.P.A) = toUnit D.P.A ≫ η[D.P.A]` using `rfl`.

Establish `e2 : (𝟙 D.P.A : D.P.A ⟶ D.P.A).left = 𝟙 D.P.A.left` using `rfl`. Rewrite using `[e0, e1, e2]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Normalize the expressions using the abelian group laws.

Establish `key : ∀ A B C D E Q I O : U, A * B = I⁻¹ * O → C * D = Q → E = O ^ (-1 : ℤ) → A * (B * C) * D * E = Q * I ^ (-1 : ℤ)`. Introduce `A B C D E Q I O h₁ h₂ h₃`. Rewrite using `[← _root_.mul_assoc A B C, h₁, _root_.mul_assoc _ C D, h₂, h₃]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`.

Normalize the expressions using the abelian group laws. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]`. Conclude with `key _ _ _ _ _ _ _ _ hAB hCD rfl) T0 hT0`. Take `⟨w, hw, hwv⟩` from `exists_iso_of_joinGen D.P.isLB D₀.P.isLB t ht`. Use `⟨w, hw, fun y z J J' hJ hJ' => ?_⟩` and prove the remaining obligations.

Take `⟨Jn, hJn, e1, e2⟩` from `exists_good_join D.P.isLB D₀.P.isLB hJ' hJ`. Substitute `e1 e2` using the available equality. Rewrite using `[hwv _ (D.xK y) z Jn hJn, htv _ _ z Jn hJn]`. Establish `hp₂` using `isPart_inr D.P.L D₀.P.L`. Establish `hJ1 : Good D.P.L z (rl Jn)` using `hp₁.good hJn`.

Establish `vT : val T0 (D.xK y) z Jn = val u (D.xK y) z (rl Jn) * (val κ (D.xK y) z (rl Jn))⁻¹ * (∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2)) * (val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn))⁻¹`. Simplify using `only [T0, P, rig0, val_mul hJn, val_inv, hp₁.val_gen _ _ _ hJn, val_prodZGen _ _ _ _ _ hJn, val_pull hJn, val_pull hJ1]`. Establish `c1` using `val_corr hJ1 (hu' y) (𝟙 _)`. Rewrite `c1` using `[val_mul hJ1, val_mul hJ1, val_pull hJ1, Category.id_comp]`. Establish `cE` using `hκ' (toUnit (TK R) ≫ D.c y) y (fun ab => h ab.1 (k ab.2 y)) (Category.comp_id _) (fun ab => by simp only [h1, h2, Category.assoc]) z (rl Jn) hJ1`.

Establish `hrig : D.xK y ≫ (toUnit D.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left`. Rewrite using `[Category.id_comp]`. Use `show (toUnit (TK R) ≫ D.c y).left ≫ (toUnit D.P.A).left = _`. Rewrite using `[← Over.comp_left, Category.assoc, comp_toUnit, comp_toUnit]`. Establish `vrig : val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn) = val D.rigK (𝟙 _) z (rl Jn)`.

Rewrite using `[hrig]`. Conclude with `(val_pull hJ1 _ _ _).symm`. Establish `hper : ∀ a b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z (rr Jn) = val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) * val (Γ a) (D.xK y ≫ g b) z Jn`. Introduce `a b`. Take `⟨u', hu'n, hu'v⟩` from `h3 a (k b y)`.

Rewrite using `[hu'v y z Jn hJn]`. Use `congrArg (_ * ·) ((hΓ' a (h a (k b y)) (k b y) (h1 a (k b y)) u' hu'n (TK R) (toUnit _ ≫ D.c y) z Jn hJn).trans (congrArg (fun q => val (Γ a) q z Jn) ?_))` and prove the remaining obligations. Use `show (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D₀.c (k b y))).left = (toUnit (TK R) ≫ D.c y).left ≫ (lift (𝟙 D.P.A) (pr b)).left`. Rewrite using `[h2, ← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]`. Establish `hG : ∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2) = (∏ a, ∏ b, val (Γ a) (D.xK y ≫ g b) z Jn ^ W a b)⁻¹`.

Rewrite using `[Fintype.prod_prod_type]`. Simplify using `only [zpow_neg, Finset.prod_inv_distrib]`. Establish `key2 : ∀ {V : Type} [CommGroup V] (ψ ρ Tm Uu Kk Tp Gp : V), Tm * Uu = ψ * ρ → Tm * Kk = Tp → ψ = Uu * Kk⁻¹ * Gp⁻¹ * ρ⁻¹ * (Tp * Gp)`. Introduce `V _ ψ ρ Tm Uu Kk Tp Gp e₁ e₂`. Rewrite using `[eq_inv_mul_of_mul_eq e₁, eq_inv_mul_of_mul_eq e₂]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Rewrite using `[vT, vrig, hG]`. Simplify using `only [hper, mul_zpow, Finset.prod_mul_distrib]`.

Establish `cE' : val (D.tau y (∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y))) (𝟙 _) z (rl Jn) * val κ (D.xK y) z (rl Jn) = ∏ a, ∏ b, val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) ^ W a b`. Use `Eq.trans cE ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Conclude with `key2 _ _ _ _ _ _ _ c1 cE'`.
-/
theorem tens_iso_psi : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  intro R _ _ D D₀ r W pr j h k h1 h2 h3 h4 h5 h6
  obtain ⟨u, hu, hu'⟩ := h6
  obtain ⟨κ, hκ, hκ'⟩ := h5
  choose Γ hΓ hΓ' using h4
  have hp₁ := isPart_inl D.P.L D₀.P.L
  let g : Fin r → (D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left) := fun b => (lift (𝟙 D.P.A) (pr b)).left
  let Φ : Fin r → Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ D.P.A.left ⨿ D₀.P.A.left) := fun a =>
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let P := prodZGen (JN D D₀) (fun ab : Fin r × Fin r => fun m => g ab.2 ≫ Φ ab.1 m) (fun _ => Sum.elim Oε Oinvε)
    (fun ab => -W ab.1 ab.2) (fun ab => LB.pullGen (JN D D₀) _ _ (Γ ab.1) (g ab.2))
  have hP : P.IsGen := prodZGen_isGen (jn_isLB D D₀) _ fun ab =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (hΓ ab.1) _
  let rig0 := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (toUnit D.P.A).left
  have hrig0 : rig0.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  let T0 := LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (hp₁.gen u)
    (LB.invGen (JN D D₀) _ _ (hp₁.gen κ))) P) (LB.invGen (JN D D₀) _ _ (hp₁.gen rig0))
  have hT0 : T0.IsGen := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hp₁.gen_isGen hu) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _
        (hp₁.gen_isGen hκ))) hP) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hp₁.gen_isGen hrig0))
  obtain ⟨t, ht, htv⟩ := exists_gen (jn_isLB D D₀)
    (φ' := Sum.elim (fun k => tensφ pr k ≫ coprod.inr) (fun _ : PUnit => 𝟙 D.P.A.left ≫ coprod.inl))
    (ε' := Sum.elim (tensε W) (fun _ => -1)) (by
      intro U _ hh
      clear hu' hκ' hΓ' h3 h1 h2 hT0 hP hrig0
      have cl : ∀ {T T' : Over (Sp R)} {B : Over (Sp R)} [GrpObj B] (s : T' ⟶ T) (x y : T ⟶ B) (i : Fin 4),
          s.left ≫ lamPts x y i = lamPts (s ≫ x) (s ≫ y) i := by
        intro T T' B _ s x y i
        fin_cases i
        · exact congrArg (fun q => q.left) (MonObj.comp_mul s x y)
        · rfl
        · rfl
        · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one s)
      have hD1 : ∀ a b i, g b ≫ Φ a (Sum.inl i) = lamPts (𝟙 D.P.A) (pr b ≫ j a) i ≫ coprod.inl := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) i ≫ coprod.inl = _
        rw [← Category.assoc, cl, lift_fst, lift_snd_assoc]
      have hD2 : ∀ a b i, g b ≫ Φ a (Sum.inr i) = tensφ pr ((a, b), i) ≫ coprod.inr := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) i ≫ coprod.inr = _
        rw [← Category.assoc, cl, lift_fst_assoc, lift_snd, Category.id_comp]
        rfl
      have hOi : ∀ i, Oinvε i = - Oε i := by intro i; fin_cases i <;> rfl
      have hCD : (∏ p : (Fin r × Fin r) × Fin 4,
            hh (lamPts (𝟙 D.P.A) (pr p.1.2 ≫ j p.1.1) p.2 ≫ coprod.inl) ^ (- -(W p.1.1 p.1.2 * Oε p.2))) *
          (∏ p : (Fin r × Fin r) × (Fin 4 ⊕ Fin 4), hh (g p.1.2 ≫ Φ p.1.1 p.2) ^ (-W p.1.1 p.1.2 * Sum.elim Oε Oinvε p.2)) =
          ∏ p : (Fin r × Fin r) × Fin 4, hh (tensφ pr p ≫ coprod.inr) ^ (tensε W p) := by
        rw [Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r),
          Fintype.prod_prod_type (α₁ := Fin r × Fin r), ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ab _ => ?_
        rw [Fintype.prod_sum_type, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hD1, hD2, Sum.elim_inl, Sum.elim_inr, hOi]
        simp only [tensε, neg_neg, neg_mul, mul_neg, zpow_neg, mul_inv_cancel, _root_.one_mul, Prod.mk.eta]
      have hAB : (∏ i : Fin 4, hh (![(padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)).left,
            𝟙 D.P.A.left, (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2).left, (toUnit D.P.A ≫ η[D.P.A]).left] i ≫
              coprod.inl) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) i)) *
          (∏ i : Fin 4, hh (lamPts (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) i ≫ coprod.inl) ^
            (-Oε i)) =
          (hh (𝟙 D.P.A.left ≫ coprod.inl))⁻¹ * hh ((toUnit D.P.A ≫ η[D.P.A]).left ≫ coprod.inl) := by
        simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        have e0 : (𝟙 D.P.A * ∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) =
            padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) := rfl
        have e1 : (1 : D.P.A ⟶ D.P.A) = toUnit D.P.A ≫ η[D.P.A] := rfl
        have e2 : (𝟙 D.P.A : D.P.A ⟶ D.P.A).left = 𝟙 D.P.A.left := rfl
        rw [e0, e1, e2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      have key : ∀ A B C D E Q I O : U, A * B = I⁻¹ * O → C * D = Q → E = O ^ (-1 : ℤ) →
          A * (B * C) * D * E = Q * I ^ (-1 : ℤ) := by
        intro A B C D E Q I O h₁ h₂ h₃
        rw [← _root_.mul_assoc A B C, h₁, _root_.mul_assoc _ C D, h₂, h₃]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
      exact key _ _ _ _ _ _ _ _ hAB hCD rfl) T0 hT0
  obtain ⟨w, hw, hwv⟩ := exists_iso_of_joinGen D.P.isLB D₀.P.isLB t ht
  refine ⟨w, hw, fun y z J J' hJ hJ' => ?_⟩
  obtain ⟨Jn, hJn, e1, e2⟩ := exists_good_join D.P.isLB D₀.P.isLB hJ' hJ
  subst e1 e2
  rw [hwv _ (D.xK y) z Jn hJn, htv _ _ z Jn hJn]
  have hp₂ := isPart_inr D.P.L D₀.P.L
  have hJ1 : Good D.P.L z (rl Jn) := hp₁.good hJn
  have vT : val T0 (D.xK y) z Jn = val u (D.xK y) z (rl Jn) * (val κ (D.xK y) z (rl Jn))⁻¹ *
      (∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2)) *
      (val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn))⁻¹ := by
    simp only [T0, P, rig0, val_mul hJn, val_inv, hp₁.val_gen _ _ _ hJn, val_prodZGen _ _ _ _ _ hJn, val_pull hJn,
      val_pull hJ1]
  have c1 := val_corr hJ1 (hu' y) (𝟙 _)
  rw [val_mul hJ1, val_mul hJ1, val_pull hJ1, Category.id_comp] at c1
  have cE := hκ' (toUnit (TK R) ≫ D.c y) y (fun ab => h ab.1 (k ab.2 y)) (Category.comp_id _)
    (fun ab => by simp only [h1, h2, Category.assoc]) z (rl Jn) hJ1
  have hrig : D.xK y ≫ (toUnit D.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c y).left ≫ (toUnit D.P.A).left = _
    rw [← Over.comp_left, Category.assoc, comp_toUnit, comp_toUnit]
  have vrig : val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn) = val D.rigK (𝟙 _) z (rl Jn) := by
    rw [hrig]; exact (val_pull hJ1 _ _ _).symm
  have hper : ∀ a b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z (rr Jn) =
      val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) * val (Γ a) (D.xK y ≫ g b) z Jn := by
    intro a b
    obtain ⟨u', hu'n, hu'v⟩ := h3 a (k b y)
    rw [hu'v y z Jn hJn]
    refine congrArg (_ * ·) ((hΓ' a (h a (k b y)) (k b y) (h1 a (k b y)) u' hu'n (TK R) (toUnit _ ≫ D.c y) z Jn hJn).trans
      (congrArg (fun q => val (Γ a) q z Jn) ?_))
    show (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D₀.c (k b y))).left =
      (toUnit (TK R) ≫ D.c y).left ≫ (lift (𝟙 D.P.A) (pr b)).left
    rw [h2, ← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
  have hG : ∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2) =
      (∏ a, ∏ b, val (Γ a) (D.xK y ≫ g b) z Jn ^ W a b)⁻¹ := by
    rw [Fintype.prod_prod_type]; simp only [zpow_neg, Finset.prod_inv_distrib]
  have key2 : ∀ {V : Type} [CommGroup V] (ψ ρ Tm Uu Kk Tp Gp : V), Tm * Uu = ψ * ρ → Tm * Kk = Tp →
      ψ = Uu * Kk⁻¹ * Gp⁻¹ * ρ⁻¹ * (Tp * Gp) := by
    intro V _ ψ ρ Tm Uu Kk Tp Gp e₁ e₂
    rw [eq_inv_mul_of_mul_eq e₁, eq_inv_mul_of_mul_eq e₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [vT, vrig, hG]
  simp only [hper, mul_zpow, Finset.prod_mul_distrib]
  have cE' : val (D.tau y (∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y))) (𝟙 _) z (rl Jn) *
      val κ (D.xK y) z (rl Jn) = ∏ a, ∏ b, val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) ^ W a b := by
    refine Eq.trans cE ?_
    rw [Fintype.prod_prod_type]
  exact key2 _ _ _ _ _ _ _ c1 cE'

end GlobalTheory.Mum.PowData
