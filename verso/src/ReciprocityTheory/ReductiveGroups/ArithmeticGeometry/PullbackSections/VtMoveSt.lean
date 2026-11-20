import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSym

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Rewrite using `[← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id]`.
-/
theorem snd_pow_left {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) (N : ℕ) :
    (snd T A ^ N).left = (snd T A).left ≫ (mulA A N).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem sval_zc {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨t₀', α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩` from `h`. Establish `h1 : (liftPt m.cart τ hτ t₀').left ≫ m.φ = τ ≫ t₀'.left` using `liftPt_left m.cart τ hτ t₀'`. Establish `ht1 : liftPt m.cart τ hτ t₀' ^ N = liftPt m.cart τ hτ tt` using `pt_ext m.cart ((pow_rel m.cart τ hτ h1 N).trans (by rw [ht]; exact (liftPt_left m.cart τ hτ tt).symm))`. Establish `o1 : liftPt m.cart τ hτ t₀' ^ (N ^ 2) = 1` using `pow_eq_one m.cart τ hτ h1 (hok _ o)`. Take `⟨α₀', g₀', pm₀, n₀'⟩` from `mulGen_move m w hw N α₀ g₀ n₀`.

Establish `eα : ∀ k, (![(snd T₀ t.G).left, (snd T₀ t.G ^ N).left] : Fin 2 → _) k = (snd T₀ t.G).left ≫ (![𝟙 t.G.left, (mulA t.G N).left] : Fin 2 → _) k` using `fun k => by fin_cases k`. Conclude with `(Category.comp_id _).symm`. Conclude with `snd_pow_left _ _ _`. Take `⟨α₁, gα₁, Hα₁⟩` from `exists_gen_pull (L := t.PP.L) ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1] α₀ (snd T₀ t.G).left _ eα`. Establish `gα` using `gα₁ g₀`.

Establish `vα : ∀ y J, Good t.PP.L y J → val α (𝟙 _) y J = val α₁ (𝟙 _) y J` using `fun y J hJ => (val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_of_pull eα Hα₁ _ y hJ).symm)`. Establish `tw' : IsTwistPull t.G t.PP.L (mulT t.G T₀ N) (snd T₀ t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α₁ s₀ s₁` using `twist_of_val t.PP.isLB gα fun y J hJ => (twist_val tw (𝟙 _) y hJ).trans (by rw [vα y J hJ, Category.id_comp])`. Take `⟨α', gα', pmα, cα'⟩` from `MixEnd.genSnd_move m.cart τ hτ t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1) (mulA t'.G N).left (mulA t.G N).left (mulA_push m.cart N) ![(N : ℤ) ^ 2, -1] α₀' α₀ pm₀ (snd T t'.G ^ N) (snd T₀ t.G ^ N) (snd_pow_left _ _ _) (snd_pow_left _ _ _) _ gα (corr_of_val t.PP.isLB fun y J hJ …`. Take `⟨s₁', tw1, hs1⟩` from `twist_move m.cart τ hτ t'.PP.isLB w (ψA := mulT t'.G T N) (mA := snd T t'.G ^ N) (lift_snd _ _) (mulT_push m.cart τ hτ N) (snd_pow_push m.cart τ hτ N) gα' pmα tw' hs`. Take `⟨U', sl', pmU⟩` from `symLift_move m.cart τ hτ t.PP.isLB t'.PP.isLB w hw.1 sl (hok _ o) h1`.

Establish `hxU : τ ≫ U.pt.left = U'.pt.left ≫ m.φ` using `by rw [sl.pt_eq, sl'.pt_eq]; exact h1.symm`. Take `⟨F', ac', hF⟩` from `twist_move m.cart τ hτ t'.PP.isLB w (ψA := translT t'.G U'.pt) (mA := translPt t'.G U'.pt) (lift_snd _ _) (psi_transl m.cart τ hτ U'.pt U.pt hxU) (psi_tr m.cart τ hτ U'.pt U.pt hxU).symm U'.isGen pmU ac hs1`. Conclude with `⟨F', ⟨liftPt m.cart τ hτ t₀', α₀', α', s₁', U', ht1, o1, g₀', n₀', cα', tw1, sl', ac'⟩, hF⟩`.
-/
theorem vtOver_move {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) (N : ℕ) {ok : (T₀ ⟶ t.G) → Prop} (hok : ∀ u, ok u → u ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow t.G t.PP.L 1 T₀)} {tt : T₀ ⟶ t.G} {F : LB.Sec (LPow t.G t.PP.L ((N : ℤ) ^ 2) T₀)}
    (h : IsVtOver t.G t.PP N ok s₀ tt F) {s : LB.Sec (LPow t'.G t'.PP.L 1 T)} (hs : TieT m.cart τ hτ w 1 s₀ s) :
    ∃ F' : LB.Sec (LPow t'.G t'.PP.L ((N : ℤ) ^ 2) T),
      IsVtOver t'.G t'.PP N (fun u => u ^ (N ^ 2) = 1) s (liftPt m.cart τ hτ tt) F' ∧
        TieT m.cart τ hτ w ((N : ℤ) ^ 2) F F' := by
  obtain ⟨t₀', α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩ := h
  have h1 : (liftPt m.cart τ hτ t₀').left ≫ m.φ = τ ≫ t₀'.left := liftPt_left m.cart τ hτ t₀'
  have ht1 : liftPt m.cart τ hτ t₀' ^ N = liftPt m.cart τ hτ tt :=
    pt_ext m.cart ((pow_rel m.cart τ hτ h1 N).trans (by rw [ht]; exact (liftPt_left m.cart τ hτ tt).symm))
  have o1 : liftPt m.cart τ hτ t₀' ^ (N ^ 2) = 1 := pow_eq_one m.cart τ hτ h1 (hok _ o)
  obtain ⟨α₀', g₀', pm₀, n₀'⟩ := mulGen_move m w hw N α₀ g₀ n₀
  have eα : ∀ k, (![(snd T₀ t.G).left, (snd T₀ t.G ^ N).left] : Fin 2 → _) k =
      (snd T₀ t.G).left ≫ (![𝟙 t.G.left, (mulA t.G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.comp_id _).symm
    · exact snd_pow_left _ _ _
  obtain ⟨α₁, gα₁, Hα₁⟩ := exists_gen_pull (L := t.PP.L) ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1] α₀
    (snd T₀ t.G).left _ eα
  have gα := gα₁ g₀
  have vα : ∀ y J, Good t.PP.L y J → val α (𝟙 _) y J = val α₁ (𝟙 _) y J := fun y J hJ =>
    (val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_of_pull eα Hα₁ _ y hJ).symm)
  have tw' : IsTwistPull t.G t.PP.L (mulT t.G T₀ N) (snd T₀ t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α₁ s₀ s₁ :=
    twist_of_val t.PP.isLB gα fun y J hJ => (twist_val tw (𝟙 _) y hJ).trans (by rw [vα y J hJ, Category.id_comp])
  obtain ⟨α', gα', pmα, cα'⟩ := MixEnd.genSnd_move m.cart τ hτ t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1)
    (mulA t'.G N).left (mulA t.G N).left (mulA_push m.cart N) ![(N : ℤ) ^ 2, -1] α₀' α₀ pm₀ (snd T t'.G ^ N)
    (snd T₀ t.G ^ N) (snd_pow_left _ _ _) (snd_pow_left _ _ _) _ gα
    (corr_of_val t.PP.isLB fun y J hJ => (val_of_pull eα Hα₁ _ y hJ).trans (val_pull hJ _ _ _).symm)
  obtain ⟨s₁', tw1, hs1⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := mulT t'.G T N) (mA := snd T t'.G ^ N)
    (lift_snd _ _) (mulT_push m.cart τ hτ N) (snd_pow_push m.cart τ hτ N) gα' pmα tw' hs
  obtain ⟨U', sl', pmU⟩ := symLift_move m.cart τ hτ t.PP.isLB t'.PP.isLB w hw.1 sl (hok _ o) h1
  have hxU : τ ≫ U.pt.left = U'.pt.left ≫ m.φ := by rw [sl.pt_eq, sl'.pt_eq]; exact h1.symm
  obtain ⟨F', ac', hF⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := translT t'.G U'.pt)
    (mA := translPt t'.G U'.pt) (lift_snd _ _) (psi_transl m.cart τ hτ U'.pt U.pt hxU)
    (psi_tr m.cart τ hτ U'.pt U.pt hxU).symm U'.isGen pmU ac hs1
  exact ⟨F', ⟨liftPt m.cart τ hτ t₀', α₀', α', s₁', U', ht1, o1, g₀', n₀', cα', tw1, sl', ac'⟩, hF⟩

/- English proof (translation)
Introduce `E _ _ _ H X₀ t₀ K _ x tK m1 w1 hw N ok s tt F hF hok sK hsK`. Establish `hfst : ∀ {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left), r ≫ (fst (𝟙_ (Over (Sp K))) tK.G).left ≫ (𝟙_ (Over (Sp K))).hom = (r ≫ (snd _ tK.G).left) ≫ tK.G.hom`. Introduce `Z r`. Rewrite using `[Over.w (fst _ _), Category.assoc, Over.w (snd _ _)]`. Establish `hs : TieT m1.cart (T₀` using `Over.mk x) (𝟙_ (Over (Sp K))).hom rfl w1 1 s (zCast tK.G Nat.cast_one sK) := by`.

Introduce `Z r z J₀ J hJ₀ hJ`. Establish `e` using `hsK Z (r ≫ (snd _ tK.G).left) (r ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left) r (by rw [Category.assoc, psi_snd, Category.assoc]) (by rw [Category.assoc, psi_fst]; exact hfst r) rfl z J₀ J hJ₀ hJ`. Rewrite `e` using `[sval_zc, Category.comp_id]`. Rewrite using `[sval_zc, e, zpow_one, pow_one]`. Both sides reduce to the same expression.

Take `⟨F', hV, hT⟩` from `vtOver_move m1 w1 hw (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl N hok hF hs`. Use `⟨_, F', hV, fun Z r zp zp' h1 h2 h3 z J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Substitute `h3` using the available equality. Take `rfl : zp = zp' ≫ (psiO m1.cart (T₀` from `Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left := by`. Use `hom_ext₀ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, psi_fst, h2, hfst]`. Rewrite using `[Category.assoc, psi_snd, h1, Category.assoc]`. Rewrite using `[sval_zc, sval_zc, hT Z zp' z J J' hJ hJ', Category.comp_id]`. Use `congr 1`.
-/
theorem vtMoveSt : VtMoveSt := by
  intro E _ _ _ H X₀ t₀ K _ x tK m1 w1 hw N ok s tt F hF hok sK hsK
  have hfst : ∀ {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
      r ≫ (fst (𝟙_ (Over (Sp K))) tK.G).left ≫ (𝟙_ (Over (Sp K))).hom = (r ≫ (snd _ tK.G).left) ≫ tK.G.hom := by
    intro Z r
    rw [Over.w (fst _ _), Category.assoc, Over.w (snd _ _)]
  have hs : TieT m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl w1 1 s (zCast tK.G Nat.cast_one sK) := by
    intro Z r z J₀ J hJ₀ hJ
    have e := hsK Z (r ≫ (snd _ tK.G).left) (r ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left) r
      (by rw [Category.assoc, psi_snd, Category.assoc])
      (by rw [Category.assoc, psi_fst]; exact hfst r) rfl z J₀ J hJ₀ hJ
    rw [sval_zc, Category.comp_id] at e
    rw [sval_zc, e, zpow_one, pow_one]
    rfl
  obtain ⟨F', hV, hT⟩ := vtOver_move m1 w1 hw (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl N hok hF hs
  refine ⟨_, F', hV, fun Z r zp zp' h1 h2 h3 z J J' hJ hJ' => ?_⟩
  subst h3
  obtain rfl : zp = zp' ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left := by
    refine hom_ext₀ ?_ ?_
    · rw [Category.assoc, psi_fst, h2, hfst]
    · rw [Category.assoc, psi_snd, h1, Category.assoc]
  rw [sval_zc, sval_zc, hT Z zp' z J J' hJ hJ', Category.comp_id]
  congr 1

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
