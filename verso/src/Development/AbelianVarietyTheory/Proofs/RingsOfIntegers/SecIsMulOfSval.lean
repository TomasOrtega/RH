import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevelOneIdeal

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨e, he⟩` from `exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)`. Take `⟨j, hj⟩` from `exists_chart_top (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)`. Establish `le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K` using `PUnit) (fun _ => (D.c χ).left) j := hj.ge`. Establish `hx : D.xK χ = jK R ≫ (D.c χ).left`.

Simplify using `[DegPre.xK, ptK]`. Establish `le' : jK R ⁻¹ᵁ ⊤ ≤ LB.wchart D.P.L (K` using `PUnit) (fun _ => D.xK χ) j := fun y _ => Set.mem_iInter.2 fun k => by`. Rewrite using `[hx]`. Conclude with `Set.mem_iInter.1 (le (show (jK R) y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) k`. Take `⟨r₀, hr₀, hψ⟩` from `h j ⊤ (isAffineOpen_top _) (le.trans (LB.wchart_le _ _ _ PUnit.unit)) le'`.

Establish `hto : ∀ a, DegPre.toOpen (R` using `R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by`. Simplify using `[DegPre.toOpen]`. Establish `hs : Function.Surjective (DegPre.toOpen (R` using `R) ⊤) := fun x => by`. Take `⟨a, ha⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x`. Conclude with `⟨a, (hto a).trans ha⟩`.

Take `⟨a₀, ha₀, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ hs).1 hr₀`. Take `⟨b, hb⟩` from `hs (res le (e.s j))⁻¹.val`. Use `⟨e, he, a₀ * b, I.mul_mem_right _ ha₀, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `m₁ : r z ∈ LB.wchart D.P.L (K` using `PUnit) (fun _ => D.xK χ) j := le' trivial`. Establish `m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K` using `PUnit) (fun _ => (D.c χ).left) j := le trivial`.

Establish `e₁ : val (D.psi χ) r z J = _` using `gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁`. Establish `e₂ : val e (r ≫ jK R) z J = _` using `gen_trans he (r ≫ jK R) z (hJ.mem _ _) m₂`. Establish `e₃ : trF (L` using `D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j = trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by`. Establish `hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left` using `(congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm`. Simplify using `only [trF]`.

Rewrite using `[hq]`. Establish `e₄ : (gm r z (LB.wchart D.P.L (K` using `PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = cst (r ≫ jK R) z a₀ := by`. Use `(gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)` and prove the remaining obligations. Use `(congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)` and prove the remaining obligations. Rewrite using `[hto]`.

Both sides reduce to the same expression. Establish `e₅ : cst (r ≫ jK R) z b * (gm (r ≫ jK R) z (LB.wchart D.P.L (K` using `PUnit) (fun _ => (D.c χ).left) j) (e.s j)).val = 1 := by`. Rewrite using `[cst, ← hto, hb, gs_unit _ z ⊤ trivial, map_inv]`. Conclude with `(congrArg₂ (fun q c => q⁻¹.val * c) (gm_res (r ≫ jK R) z le trivial (e.s j)) rfl).trans (Units.inv_mul _)`. Establish `e₆ : cst (r ≫ jK R) z (a₀ * b) = cst (r ≫ jK R) z a₀ * cst (r ≫ jK R) z b`.

Rewrite using `[cst, map_mul, gs_mul _ z ⊤ trivial]`. Both sides reduce to the same expression. Rewrite using `[e₁, e₂, e₆, Units.val_mul, Units.val_mul]`. Use `erw [e₃, e₄]`. Take the linear combination `(-(cst (r ≫ jK R) z a₀ * (trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j).val)) * e₅`.
-/
theorem exists_psi_val {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (D : DegPre R) (χ : D.X)
    (h : D.PsiIn χ I) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧ ∃ a ∈ I,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = cst (r ≫ jK R) z a * (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj⟩ := exists_chart_top (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := hj.ge
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ ⊤ ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact Set.mem_iInter.1 (le (show (jK R) y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) k
  obtain ⟨r₀, hr₀, hψ⟩ := h j ⊤ (isAffineOpen_top _) (le.trans (LB.wchart_le _ _ _ PUnit.unit)) le'
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := fun x => by
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    exact ⟨a, (hto a).trans ha⟩
  obtain ⟨a₀, ha₀, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hr₀
  obtain ⟨b, hb⟩ := hs (res le (e.s j))⁻¹.val
  refine ⟨e, he, a₀ * b, I.mul_mem_right _ ha₀, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e (r ≫ jK R) z J = _ := gen_trans he (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = cst (r ≫ jK R) z a₀ := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : cst (r ≫ jK R) z b *
      (gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) (e.s j)).val = 1 := by
    rw [cst, ← hto, hb, gs_unit _ z ⊤ trivial, map_inv]
    exact (congrArg₂ (fun q c => q⁻¹.val * c) (gm_res (r ≫ jK R) z le trivial (e.s j)) rfl).trans (Units.inv_mul _)
  have e₆ : cst (r ≫ jK R) z (a₀ * b) = cst (r ≫ jK R) z a₀ * cst (r ≫ jK R) z b := by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  rw [e₁, e₂, e₆, Units.val_mul, Units.val_mul]
  erw [e₃, e₄]
  linear_combination (-(cst (r ≫ jK R) z a₀ * (trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j).val)) * e₅

/- English proof (translation)
Establish `C : IsCub (th D z J)` using `isCub_cubV D.cub hJ`. Establish `t0` using `tau_mul σ hJ hB 0 0 χ`. Rewrite `t0` using `[add_zero, cPoint_zero, C.face, _root_.mul_one]`. Establish `τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R` using `R) F) z J = 1 := mul_eq_left.1 t0.symm`. Rewrite using `[val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul, pow_one, pow_one]`.
-/
theorem val_famMult_one {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 1 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul, pow_one, pow_one]

/- English proof (translation)
Introduce `j`. Use `hinj _ (fn_ext fun y hy => ?_)` and prove the remaining obligations. Use `choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)`. Establish `hJ' : Good L y J` using `hJ`. Establish `hy' : h y ∈ LB.wchart L φ j` using `hy`.

Establish `m` using `hJ'.mem φ h`. Establish `e₃ : gs h y (LB.wchart L φ j) (Out.resTop _ (scal p a)) = cst (h ≫ p) y a` using `(gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)`. Use `(gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Use `(sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)` and prove the remaining obligations.

Conclude with `(congrArg _ (H y J hJ')).trans (mul_left_comm _ _ _)`.
-/
theorem secIsMul_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) {a : R}
    {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : ∀ y J, Good L y J → sval s' h y J = cst (h ≫ p) y a * sval s h y J) : SecIsMul p a s' s := by
  intro j
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : h y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ h
  have e₃ : gs h y (LB.wchart L φ j) (Out.resTop _ (scal p a)) = cst (h ≫ p) y a :=
    (gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  rw [Category.id_comp]
  refine (sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans
    (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)
  exact (congrArg _ (H y J hJ')).trans (mul_left_comm _ _ _)

/- English proof (translation)
Introduce `hG R _ _ _ I D E g hg χ hχ`. Establish `hL` using `D.toPre.P.isLB`. Take `⟨e, he, a, ha, hψ⟩` from `exists_psi_val D.toPre χ (D.psi_pos χ hχ)`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. It suffices to establish `H : ∃ g' : D.toPre.SecB 1 (0 + 1 • χ), SecIsMul D.toPre.P.A.hom a (g (0 + 1 • χ)) g' by`.

Rewrite `H` using `[zero_add, one_smul]`. Then use the resulting hypothesis. Establish `c₁ : D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left` using `by simp [SectionScalarValuation.cQ]`. Establish `c₂ : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left`. Rewrite using `[Hom.one_def]`. Simplify using `[eSec]`.

Establish `c₃ : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1` using `cPoint_zero (D := D.toPre) _`. Take `⟨eB, heB, veB⟩` from `SectionScalarValuation.exists_eB D.toPre 1 0 χ (LB.mulGen D.toPre.P.L _ _ _ _ e D.toPre.rig) (mulGen_isGen _ _ _ _ _ _ _ he D.toPre.rig_gen) (fun U _ h => by`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, c₃, _root_.one_mul]`. Use the proof step `simp)`. Establish `hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i) (Sum.elim (D.toPre.famφB (0 + 1 • χ)) (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i))) (Sum.elim …` using `fun U _ h => by`.

Rewrite using `[Fintype.prod_sum_type, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]`. Rewrite using `[mul_left_comm, mul_inv_cancel, _root_.mul_one]`. Take `⟨g', hg'⟩` from `exists_sec hL hformB (pullMulSec (g 0) (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left eB heB)`. Use `⟨g', secIsMul_of_sval hL _ (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩` and prove the remaining obligations.

Take `⟨⟨u, hu, hc⟩, hv⟩` from `gen_fe (D := D.toPre) (F := FractionRing R) hG 1 χ 0`. Establish `vu` using `hv u hu hc _ (𝟙 _) y J hJ`. Establish `hrel` using `(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (E.fe χ 0 u hu hc) _ (𝟙 _) y J hJ`. Establish `htr : (DegPre.trF D.toPre (FractionRing R) χ).left ≫ (DegPre.prB D.toPre (FractionRing R)).left = (DegPre.prB D.toPre (FractionRing R)).left ≫ (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`.

Use `congr 1`. Rewrite using `[DegPre.trF, DegPre.prB, lift_snd, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]`. Both sides reduce to the same expression. Rewrite `hrel` using `[H1.sval_scal (hg _) _ y hJ, H1.sval_scal (hg _) _ y hJ, Category.id_comp, Category.id_comp, htr]`. Rewrite using `[hrel, hg' _ _ y J hJ, sval_pullMulSec _ _ _ heB _ y hJ, mul_left_comm]`.

Use `congr 1`. Establish `w₁ : (fst (TF (R` using `R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R = (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom := (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing R))).symm`. Establish `v₁` using `veB _ (DegPre.prB D.toPre (FractionRing R)) y J hJ`. Establish `v₂` using `hψ _ ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ`. Establish `v₃ : val D.toPre.rigK ((fst (TF (R` using `R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J = val D.toPre.rig ((DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom) y J := by`.

Rewrite using `[← w₁, ← Category.assoc]`. Conclude with `val_pull hJ _ _ _`. Rewrite `v₂` using `[Category.assoc, w₁]`. Rewrite `vu` using `[Over.id_left, Category.id_comp, val_famMult_one D.tau_bimult _ hJ, v₃, uVal, Category.id_comp, Category.id_comp, comp_cP]`. Rewrite `v₁` using `[val_mul hJ]`.

Rewrite using `[vu, v₁]`. Simplify using `only [Units.val_mul]`. Rewrite using `[v₂]`. Simplify using `only [SectionScalarValuation.cQ, cP, th]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (E : Fam D.toPre (FractionRing R) 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (E.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ χ, χ ≠ 0 → ∃ a ∈ I, ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom a (g χ) g' := by
  intro hG R _ _ _ I D E g hg χ hχ
  have hL := D.toPre.P.isLB
  obtain ⟨e, he, a, ha, hψ⟩ := exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  refine ⟨a, ha, ?_⟩
  suffices H : ∃ g' : D.toPre.SecB 1 (0 + 1 • χ), SecIsMul D.toPre.P.A.hom a (g (0 + 1 • χ)) g' by
    rwa [zero_add, one_smul] at H
  have c₁ : D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by simp [SectionScalarValuation.cQ]
  have c₂ : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have c₃ : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1 := cPoint_zero (D := D.toPre) _
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre 1 0 χ (LB.mulGen D.toPre.P.L _ _ _ _ e D.toPre.rig)
    (mulGen_isGen _ _ _ _ _ _ _ he D.toPre.rig_gen) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, c₃, _root_.one_mul]
      simp)
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)
      (Sum.elim (D.toPre.famφB (0 + 1 • χ))
        (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)))
      (Sum.elim (DegPre.famε 1) (DegPre.deltaε 1)) (D.toPre.famφB (0 + 1 • χ)) (DegPre.famε 1) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨g', hg'⟩ := exists_sec hL hformB
    (pullMulSec (g 0) (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left eB heB)
  refine ⟨g', secIsMul_of_sval hL _ (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG 1 χ 0
  have vu := hv u hu hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (E.fe χ 0 u hu hc) _ (𝟙 _) y J hJ
  have htr : (DegPre.trF D.toPre (FractionRing R) χ).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [DegPre.trF, DegPre.prB, lift_snd, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
    rfl
  rw [H1.sval_scal (hg _) _ y hJ, H1.sval_scal (hg _) _ y hJ, Category.id_comp, Category.id_comp, htr] at hrel
  rw [hrel, hg' _ _ y J hJ, sval_pullMulSec _ _ _ heB _ y hJ, mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing R))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
  have v₂ := hψ _ ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
  have v₃ : val D.toPre.rigK ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J =
      val D.toPre.rig ((DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom) y J := by
    rw [← w₁, ← Category.assoc]
    exact val_pull hJ _ _ _
  rw [Category.assoc, w₁] at v₂
  rw [Over.id_left, Category.id_comp, val_famMult_one D.tau_bimult _ hJ, v₃, uVal, Category.id_comp, Category.id_comp,
    comp_cP] at vu
  rw [val_mul hJ] at v₁
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

end GlobalTheory.LevelOneIdeal
