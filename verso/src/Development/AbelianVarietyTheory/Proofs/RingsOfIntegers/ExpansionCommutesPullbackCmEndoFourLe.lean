import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSectionGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemBasicOpenIffGs
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpansion

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `key : ∀ j : K → L.ι, a.f j = (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from b.f j)` using `fun j => fn_ext (V := LB.wchart L φ j) fun y hy => by choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)`. Establish `hI' : Good L y I` using `hI`. Use `Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y le_top hy c) (sec_trans b (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))))).symm` and prove the remaining obligations. Use `(sec_trans a (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans ?_` and prove the remaining obligations. Conclude with `(congrArg _ (h y I hI')).trans (mul_left_comm _ _ _)`.

Establish `hm` using `hJ.mem φ r`. Conclude with `(congrArg (gs r z _) (key _)).trans ((gs_mul r z _ hm _ _).trans (congrArg (· * sval b r z J) (gs_res r z le_top hm c)))`.
-/
theorem sval_eq_mul_of_id {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → sval a (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval b (𝟙 Y) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval a r z J = gs r z ⊤ c * sval b r z J := by
  have key : ∀ j : K → L.ι, a.f j =
      (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from b.f j) := fun j =>
    fn_ext (V := LB.wchart L φ j) fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hI' : Good L y I := hI
      refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y le_top hy c)
        (sec_trans b (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))))).symm
      refine (sec_trans a (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans ?_
      exact (congrArg _ (h y I hI')).trans (mul_left_comm _ _ _)
  have hm := hJ.mem φ r
  exact (congrArg (gs r z _) (key _)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg (· * sval b r z J) (gs_res r z le_top hm c)))

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem unitK_snd : unitK (G := G) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := pullback.lift_snd _ _ _

/- English proof (translation)
Establish `he : eSec G ≫ f.left = eSec G`. Simplify using `only [eSec, ← Over.comp_left, IsMonHom.one_hom]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [unitK, endK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]`. Conclude with `congrArg (jK V ≫ ·) he`.

Simplify using `only [unitK, endK, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]`.
-/
theorem unitK_endK (f : G ⟶ G) [IsMonHom f] : unitK (G := G) ≫ endK f = unitK := by
  have he : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply pullback.hom_ext
  · simp only [unitK, endK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact congrArg (jK V ≫ ·) he
  · simp only [unitK, endK, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

end

/- English proof (translation)
Introduce `hLaws V _ _ _ E _ _ _ H t P a N hN hN0`. Use `letI := H.starRing`. Introduce `k hk s F hs s' hs'`. Take `⟨uΨ, huΨ, -, -⟩` from `P.w0`. Establish `hM : P.D.toPre.P.L.IsLB` using `P.D.toPre.P.isLB`.

Establish `hL : P.U.LG.L.IsLB` using `P.U.LG.isLB`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hkN : 1 ≤ k * N` using `Nat.mul_pos hk1 hN0`. Use `choose Fx hFx hFu using (P.U.expand k hk1).1`. Use `choose Fp hFp using fun F : Fam P.D.toPre (FractionRing V) k => exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)`.

Use `choose sp hsp _ using (P.U.expand (k * N) hkN).2`. Take `rfl : F = Fx s` from `hFu s F hs`. Use `⟨Fp (Fx s), ?_, hFp _⟩` and prove the remaining obligations. Take `⟨u, hu, hn, hrel⟩` from `hs'`. Use `haveI : IsMonHom (t.act.act a) := t.act.hom a`.

Establish `hF : FormEq (fun _ : Fin 1 => gK (G` using `t.G)) (fun _ => ((k * N : ℕ) : ℤ)) (Sum.elim (fun _ : Fin 1 => endK (t.act.act a) ≫ gK) ![gK, endK (t.act.act a) ≫ gK]) (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := fun U _ g => by`. Simplify using `only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]`. Rewrite using `[mul_left_comm, mul_inv_cancel, _root_.mul_one]`. Take `⟨c, hc⟩` from `GlobalTheory.SectionRatio.ratio_glue _ _ P.U.LG.L hL _ _ _ _ _ (fun _ : Fin 1 => gK) _ _ _ (endK (t.act.act a)) hF u hu (P.U.SecK k) (fun s₀ => sp (Fp (Fx s₀))) (fun s₀ => s₀) (fun y J hJ => GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPr …`. Establish `e` using `GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 k i _ _ _ (hFx i) (hsp _) (hFp _) k i' _ _ _ (hFx i') (hsp _) (hFp _) 1 1 rfl y J hJ`.

Simplify `e)` using `only [pow_one]`. Take `⟨c₀, rfl⟩` from `(GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ P.D P.A t.G P.U.toUnifPre).1 c`. Establish `hF'` using `fun (U : Type) (i : CommGroup U) g => (@hF U i g).symm`. Establish `hc₀ : c₀ = 1` using `fn_ext (V := ⊤) fun y _ => by choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart hL (χ y)`. Establish `hJ' : Good P.U.LG.L y J` using `hJ`.

Take `⟨s₀, hs₀⟩` from `GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _ unitK y J hJ'`. Take `⟨b, hb⟩` from `exists_sec hL hF' (pullMulSec s₀ (endK (t.act.act a)) u hu)`. Establish `e₁` using `sval_eq_mul_of_id hL (sp (Fp (Fx s₀))) b _ (fun y J hJ => by`. Rewrite using `[hb _ _ y J hJ, sval_pullMulSec _ _ u hu _ y hJ, Category.id_comp]`. Conclude with `hc s₀ y J hJ) unitK y J hJ'`.

Rewrite `e₁` using `[hb _ _ y J hJ', sval_pullMulSec _ _ u hu _ y hJ', unitK_endK]`. Establish `e₂` using `GlobalTheory.T.value_at_unitSection_genericFibre hLaws V E H t P a N hN hN0 k s₀ _ _ _ (hFx s₀) (hsp _) (hFp _) y J hJ'`. Establish `e₃ : val u unitK y J = val (L` using `P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1)) := by`. Establish `e` using `val_corr hJ' hn (𝟙 _)`. Rewrite `e` using `[val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp, val_pow]`.

Conclude with `e`. Establish `e₄ : gs unitK y ⊤ ((pullback.snd t.G.hom (jK V)).appTop.hom c₀) = gs (𝟙 _) y ⊤ c₀` using `(gs_pull unitK (pullback.snd t.G.hom (jK V)) y ⊤ trivial c₀).trans (by rw [unitK_snd])`. Rewrite `e₁` using `[e₂, e₃, e₄]`. Rewrite using `[gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one]`. Use `(hs₀.mul (Units.isUnit (val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))))).mul_right_cancel ?_` and prove the remaining obligations.

Rewrite using `[← e₁, _root_.one_mul, mul_comm]`. Establish `hss : s' = sp (Fp (Fx s))` using `SecOps.sec_ext (sec_ext_val hL fun y J hJ => by`. Rewrite using `[(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, Category.id_comp, hc s y J hJ, hc₀, map_one, gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one, _root_.one_mul])`. Rewrite using `[hss]`. Conclude with `hsp _`.
-/
theorem expands_pull_of_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  intro hLaws V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k hk s F hs s' hs'
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN0
  choose Fx hFx hFu using (P.U.expand k hk1).1
  choose Fp hFp using fun F : Fam P.D.toPre (FractionRing V) k =>
    exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
      (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  choose sp hsp _ using (P.U.expand (k * N) hkN).2
  obtain rfl : F = Fx s := hFu s F hs
  refine ⟨Fp (Fx s), ?_, hFp _⟩
  obtain ⟨u, hu, hn, hrel⟩ := hs'
  haveI : IsMonHom (t.act.act a) := t.act.hom a
  have hF : FormEq (fun _ : Fin 1 => gK (G := t.G)) (fun _ => ((k * N : ℕ) : ℤ))
      (Sum.elim (fun _ : Fin 1 => endK (t.act.act a) ≫ gK) ![gK, endK (t.act.act a) ≫ gK])
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := fun U _ g => by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.SectionRatio.ratio_glue _ _ P.U.LG.L hL _ _ _ _ _ (fun _ : Fin 1 => gK) _ _ _
    (endK (t.act.act a)) hF u hu (P.U.SecK k) (fun s₀ => sp (Fp (Fx s₀))) (fun s₀ => s₀)
    (fun y J hJ => GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _ _ y J hJ)
    (fun i i' y J hJ => by
      have e := GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 k i _ _ _ (hFx i) (hsp _) (hFp _) k i' _ _ _ (hFx i') (hsp _)
        (hFp _) 1 1 rfl y J hJ
      simpa only [pow_one] using e)
  obtain ⟨c₀, rfl⟩ := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ P.D P.A t.G
    P.U.toUnifPre).1 c
  have hF' := fun (U : Type) (i : CommGroup U) g => (@hF U i g).symm
  have hc₀ : c₀ = 1 := fn_ext (V := ⊤) fun y _ => by
    choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart hL (χ y)
    have hJ' : Good P.U.LG.L y J := hJ
    obtain ⟨s₀, hs₀⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _
      unitK y J hJ'
    obtain ⟨b, hb⟩ := exists_sec hL hF' (pullMulSec s₀ (endK (t.act.act a)) u hu)
    have e₁ := sval_eq_mul_of_id hL (sp (Fp (Fx s₀))) b _ (fun y J hJ => by
      rw [hb _ _ y J hJ, sval_pullMulSec _ _ u hu _ y hJ, Category.id_comp]
      exact hc s₀ y J hJ) unitK y J hJ'
    rw [hb _ _ y J hJ', sval_pullMulSec _ _ u hu _ y hJ', unitK_endK] at e₁
    have e₂ := GlobalTheory.T.value_at_unitSection_genericFibre hLaws V E H t P a N hN hN0 k s₀ _ _ _ (hFx s₀) (hsp _) (hFp _) y J hJ'
    have e₃ : val u unitK y J = val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1)) := by
      have e := val_corr hJ' hn (𝟙 _)
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp, val_pow] at e
      exact e
    have e₄ : gs unitK y ⊤ ((pullback.snd t.G.hom (jK V)).appTop.hom c₀) = gs (𝟙 _) y ⊤ c₀ :=
      (gs_pull unitK (pullback.snd t.G.hom (jK V)) y ⊤ trivial c₀).trans (by rw [unitK_snd])
    rw [e₂, e₃, e₄] at e₁
    rw [gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one]
    refine (hs₀.mul (Units.isUnit (val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))))).mul_right_cancel ?_
    rw [← e₁, _root_.one_mul, mul_comm]
  have hss : s' = sp (Fp (Fx s)) := SecOps.sec_ext (sec_ext_val hL fun y J hJ => by
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, Category.id_comp, hc s y J hJ, hc₀, map_one,
      gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one, _root_.one_mul])
  rw [hss]
  exact hsp _

end GlobalTheory.PullExpansion
