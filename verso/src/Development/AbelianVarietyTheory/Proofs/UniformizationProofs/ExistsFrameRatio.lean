import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
/- English proof (translation)
The claim follows from `Subsingleton.elim (α := PrimeSpectrum F) z z'`.
-/
theorem pt_eq (z z' : (TF (R := R) F).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum F) z z'

def cstH (z : (TF (R := R) F).left) : F →+* (TF (R := R) F).left.presheaf.stalk z :=
  ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

omit [IsDomain R] in
/- English proof (translation)
The claim follows from `gs_eq (𝟙 _) z ⊤ trivial _`.
-/
theorem cst_eq (z : (TF (R := R) F).left) (x : F) : cst F z x = cstH z x :=
  gs_eq (𝟙 _) z ⊤ trivial _

omit [IsDomain R] in
/- English proof (translation)
Introduce `a`. Take `⟨U, hU, s, rfl⟩` from `(TF (R := R) F).left.presheaf.germ_exist a`. Take `rfl : U = ⊤` from `eq_top_iff.2 fun y _ => pt_eq z y ▸ hU`. Take `⟨x, hx⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s`. Conclude with `⟨x, congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom hx⟩`.
-/
theorem cstH_surj (z : (TF (R := R) F).left) : Function.Surjective (cstH (R := R) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TF (R := R) F).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom hx⟩

omit [IsDomain R] in
/- English proof (translation)
The claim follows from `(cstH (R := R) z).injective`.
-/
theorem cstH_inj (z : (TF (R := R) F).left) : Function.Injective (cstH (R := R) z) :=
  (cstH (R := R) z).injective

omit [IsDomain R] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩`.
-/
theorem exists_pt : Nonempty (TF (R := R) F).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩

/- English proof (translation)
Use `choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)`. Conclude with `⟨I, hI⟩`.
-/
theorem exists_good' {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

def trU {X Z : Scheme.{0}} (L : LB X) (z : Z) (J J' : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))

/- English proof (translation)
The claim follows from `gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)`.
-/
theorem val_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    val t r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k) * val t r z J' :=
  gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)

/- English proof (translation)
The claim follows from `sec_trans s r z (hJ.mem φ r) (hJ'.mem φ r)`.
-/
theorem sval_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    sval s r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k).val * sval s r z J' :=
  sec_trans s r z (hJ.mem φ r) (hJ'.mem φ r)

/- English proof (translation)
Take `⟨J, hJ⟩` from `exists_good' hL y₀`. Set `j₀ : K → L.ι` to `fun k => J (𝟙 Y ≫ φ k)`. Establish `h₀ : ∀ y : Y, (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j₀` using `fun y => by`. Rewrite using `[hY y]`. Conclude with `hJ.mem φ (𝟙 Y)`.

Establish `le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₀` using `fun j y hy => ⟨hy, h₀ y⟩`. Use `⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j j₀)⟩, fun j j' => unit_ext fun y hy => ?_⟩` and prove the remaining obligations. Establish `v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j j₀)) = trF φ ε (𝟙 Y) y j j₀` using `fun j hj => (gm_res (𝟙 Y) y (le j) hj _).trans (gm_linComb L φ ε (𝟙 Y) y j j₀ hj (h₀ y))`. Use `((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)` and prove the remaining obligations. Conclude with `(trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h₀ y)).symm`.
-/
theorem exists_gen_pt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (y₀ : Y) (hY : ∀ y : Y, y = y₀) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨J, hJ⟩ := exists_good' hL y₀
  let j₀ : K → L.ι := fun k => J (𝟙 Y ≫ φ k)
  have h₀ : ∀ y : Y, (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j₀ := fun y => by
    rw [hY y]; exact hJ.mem φ (𝟙 Y)
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₀ := fun j y hy => ⟨hy, h₀ y⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j j₀)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j j₀)) =
      trF φ ε (𝟙 Y) y j j₀ := fun j hj =>
    (gm_res (𝟙 Y) y (le j) hj _).trans (gm_linComb L φ ε (𝟙 Y) y j j₀ hj (h₀ y))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  exact (trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h₀ y)).symm

/- English proof (translation)
Rewrite using `[Fin.prod_univ_two]`. Use `show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) = _`. Rewrite using `[zpow_neg, zpow_natCast, zpow_natCast]`.
-/
theorem prod_line (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i = h (1 : TF (R := R) F ⟶ D.P.A).left ^ k * (h b.left ^ k)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, zpow_natCast]

/- English proof (translation)
Take `⟨z⟩` from `exists_pt (R := R) (F := F)`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB z`. Establish `e` using `(hx z J hJ).trans (hy z J hJ).symm`. Rewrite `e` using `[← Units.val_pow_eq_pow_val, Units.mul_left_inj, cst_eq, cst_eq]`. Conclude with `cstH_inj z e`.
-/
theorem isCoef_unique {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s} {x y : F}
    (hx : IsCoef k g w χ s x) (hy : IsCoef k g w χ s y) : x = y := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have e := (hx z J hJ).trans (hy z J hJ).symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_left_inj, cst_eq, cst_eq] at e
  exact cstH_inj z e

/- English proof (translation)
The claim follows from `isCoef_unique (Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) ⟨x, hx⟩) hx`.
-/
theorem coef_eq {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s : Fam D F k} {x : F}
    (hx : IsCoef k g w χ (s.s χ) x) : coef s g w χ = x :=
  isCoef_unique (Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) ⟨x, hx⟩) hx

/- English proof (translation)
Take `⟨z⟩` from `exists_pt (R := R) (F := F)`. Take `⟨J', hJ'⟩` from `exists_good' D.P.isLB z`. Take `⟨x, hx⟩` from `cstH_surj z (sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J' * (val (g.s χ) (𝟙 _) z J').val * (val w (𝟙 _) z J').val * ((rigV D (TF (R := R) F).hom z J' ^ k)⁻¹).val)`. Use `⟨x, fun z' J hJ => ?_⟩` and prove the remaining obligations. Take `rfl` from `pt_eq z z'`.

Establish `a₁` using `sval_tr s (lift (𝟙 (TF (R := R) F)) g.b).left hJ hJ'`. Establish `a₂` using `val_tr (g.isGen χ) (𝟙 _) hJ hJ'`. Establish `a₃` using `val_tr hw (𝟙 _) hJ hJ'`. Establish `a₄ : rigV D (TF (R` using `R) F).hom z J = trU D.P.L z J J' (1 : TF (R := R) F ⟶ D.P.A).left * rigV D (TF (R := R) F).hom z J' := by`. Use `(val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen (TF (R := R) F).hom hJ hJ').trans ?_` and prove the remaining obligations.

Rewrite using `[Fintype.prod_unique, zpow_one]`. Both sides reduce to the same expression. Rewrite `a₁` using `[prod_fam D F (lift (𝟙 (TF (R := R) F)) g.b) χ k (trU D.P.L z J J'), lift_snd]`. Simplify using `only [Category.id_comp] at a₂ a₃`. Rewrite `a₂` using `[prod_gt g.b χ (trU D.P.L z J J')]`.

Rewrite `a₃` using `[prod_line k g.b (trU D.P.L z J J')]`. Rewrite using `[cst_eq, hx, a₁, a₂, a₃, a₄, ← Units.val_pow_eq_pow_val, mul_comm (Units.val _) (sval _ _ _ _)]`. Simplify using `only [_root_.mul_assoc, ← Units.val_mul]`. Use `congr 2`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Use `module`.
-/
theorem exists_isCoef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s) :
    ∃ x, IsCoef k g w χ s x := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨x, hx⟩ := cstH_surj z (sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J' * (val (g.s χ) (𝟙 _) z J').val *
    (val w (𝟙 _) z J').val * ((rigV D (TF (R := R) F).hom z J' ^ k)⁻¹).val)
  refine ⟨x, fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have a₁ := sval_tr s (lift (𝟙 (TF (R := R) F)) g.b).left hJ hJ'
  have a₂ := val_tr (g.isGen χ) (𝟙 _) hJ hJ'
  have a₃ := val_tr hw (𝟙 _) hJ hJ'
  have a₄ : rigV D (TF (R := R) F).hom z J = trU D.P.L z J J' (1 : TF (R := R) F ⟶ D.P.A).left *
      rigV D (TF (R := R) F).hom z J' := by
    refine (val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
      (TF (R := R) F).hom hJ hJ').trans ?_
    rw [Fintype.prod_unique, zpow_one]; rfl
  rw [prod_fam D F (lift (𝟙 (TF (R := R) F)) g.b) χ k (trU D.P.L z J J'), lift_snd] at a₁
  simp only [Category.id_comp] at a₂ a₃
  rw [prod_gt g.b χ (trU D.P.L z J J')] at a₂
  rw [prod_line k g.b (trU D.P.L z J J')] at a₃
  rw [cst_eq, hx, a₁, a₂, a₃, a₄, ← Units.val_pow_eq_pow_val, mul_comm (Units.val _) (sval _ _ _ _)]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) (exists_isCoef g hw χ _)`.
-/
theorem isCoef_coef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s : Fam D F k) :
    IsCoef k g w χ (s.s χ) (coef s g w χ) :=
  Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) (exists_isCoef g hw χ _)

/- English proof (translation)
Establish `hm` using `hJ.mem (DegPre.famφ D F χ) (lift (𝟙 (TF (R := R) F)) b).left`. Use `(gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl)) rfl)` and prove the remaining obligations. Use `(gs_res _ z le_top hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_)` and prove the remaining obligations. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression.
-/
theorem sval_lin {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (s s' : Fam D F k) (c : F) (χ : D.X) {z : (TF (R := R) F).left} {J}
    (hJ : Good D.P.L z J) : sval ((c • s + s').s χ) (lift (𝟙 (TF (R := R) F)) b).left z J =
      cst F z c * sval (s.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J +
        sval (s'.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J := by
  have hm := hJ.mem (DegPre.famφ D F χ) (lift (𝟙 (TF (R := R) F)) b).left
  refine (gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl)) rfl)
  refine (gs_res _ z le_top hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]; rfl

/- English proof (translation)
Take `⟨z⟩` from `exists_pt (R := R) (F := F)`. Take `⟨J', hJ'⟩` from `exists_good' D.P.isLB z`. Take `⟨c, hc⟩` from `cstH_surj z (val w' (𝟙 _) z J' * (val w (𝟙 _) z J')⁻¹).val`. Use `⟨c, fun h => ?_, fun z' J hJ => ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[h, map_zero]`.

Conclude with `Units.ne_zero _ hc.symm`. Take `rfl` from `pt_eq z z'`. Rewrite using `[cst_eq, hc, val_tr hw (𝟙 _) hJ hJ', val_tr hw' (𝟙 _) hJ hJ', ← Units.val_mul]`. Use `congr 1`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_frame_ratio {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w w' : Frm D F k b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (val w' (𝟙 _) z J' * (val w (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq z z'
    rw [cst_eq, hc, val_tr hw (𝟙 _) hJ hJ', val_tr hw' (𝟙 _) hJ hJ', ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/- English proof (translation)
Introduce `R _ _ D F _ _ k g`. Take `⟨z₀⟩` from `exists_pt (R := R) (F := F)`. Use `⟨exists_gen_pt D.P.isLB z₀ (fun y => pt_eq y z₀) _ _, fun hb => ?_, fun w hw => ⟨fun χ s => ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨w, hw, hv⟩` from `exists_gen D.P.isLB (φ' := DegPre.lineφ D F g.b) (ε' := DegPre.lineε k) (fun U _ h => by rw [prod_line, hb, mul_inv_cancel]; exact Fintype.prod_empty _) (LB.oneGen D.P.L (Y := (TF (R := R) F).left)) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one …`. Conclude with `⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩`.

Take `⟨x, hx⟩` from `exists_isCoef g hw χ s`. Conclude with `⟨x, hx, fun y hy => isCoef_unique hy hx⟩`. Introduce `s s' c χ`. Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `a` using `isCoef_coef g hw χ s z J hJ`.

Establish `a'` using `isCoef_coef g hw χ s' z J hJ`. Rewrite using `[sval_lin g.b s s' c χ hJ]`. Simplify using `only [cst_eq, map_add, map_mul] at a a' ⊢`. Take the linear combination `cstH z c * a + a'`. Introduce `w' hw'`.

Take `⟨c, hc, hv⟩` from `exists_frame_ratio hw hw'`. Use `⟨c, hc, hv, fun s χ => coef_eq fun z J hJ => ?_⟩` and prove the remaining obligations. Establish `a` using `isCoef_coef g hw χ s z J hJ`. Rewrite using `[hv z J hJ]`. Simplify using `only [cst_eq, map_mul] at a ⊢`.

Take the linear combination `cstH z c * a`. Introduce `t g₀ g' w' ht hadd hv s χ`. Take `⟨hb, hs⟩` from `(isAdd_iff _ _ _).1 hadd`. Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `C : IsCub (th D (T` using `TF (R := R) F) z J) := isCub_cubV D.cub hJ`.

Establish `a` using `isCoef_coef g hw χ s z J hJ`. Establish `e` using `hs χ z J hJ`. Rewrite `hb` using `[ht.1, _root_.mul_one]`. Establish `e₀ : th D z J (cP D _ χ) g.b g₀.b = 1` using `by rw [ht.1, C.face₃]`. Rewrite `e` using `[e₀, _root_.mul_one]`.

Establish `e₁ : lift (𝟙 (TF (R` using `R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]`. Rewrite using `[hv z J hJ, e, e₁, Units.val_mul, ht.2 χ z J hJ]`. Simplify using `only [cst_eq, map_mul] at a ⊢`. Take the linear combination `cstH z (t (Multiplicative.ofAdd χ)).val * a`.
-/
theorem coef_basic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F), (∃ w : Frm D F k g.b, w.IsGen) ∧ (g.b = 1 → ∃ w : Frm D F k g.b, FrmOne w) ∧ ∀ w : Frm D F k g.b, w.IsGen → (∀ χ s, ∃! x, IsCoef k g w χ s x) ∧ (∀ (s s' : Fam D F k) (c : F) χ, coef (c • s + s') g w χ = c * coef s g w χ + coef s' g w χ) ∧ (∀ w' : Frm D F k g.b, w'.IsGen → ∃ c : F, c ≠ 0 ∧ (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) ∧ ∀ (s : Fam D F k) χ, coef s g w' χ = c * coef s g w χ) ∧ ∀ (t : Multiplicative D.X →* Fˣ) (g₀ g' : GtPtF D F) (w' : Frm D F k g'.b), IsTor t g₀ → g.IsAdd g₀ g' → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) → ∀ (s : Fam D F k) χ, coef s g' w' χ = (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  intro R _ _ D F _ _ k g
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  refine ⟨exists_gen_pt D.P.isLB z₀ (fun y => pt_eq y z₀) _ _, fun hb => ?_, fun w hw => ⟨fun χ s => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F g.b) (ε' := DegPre.lineε k)
      (fun U _ h => by rw [prod_line, hb, mul_inv_cancel]; exact Fintype.prod_empty _)
      (LB.oneGen D.P.L (Y := (TF (R := R) F).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  · obtain ⟨x, hx⟩ := exists_isCoef g hw χ s
    exact ⟨x, hx, fun y hy => isCoef_unique hy hx⟩
  · intro s s' c χ
    refine coef_eq fun z J hJ => ?_
    have a := isCoef_coef g hw χ s z J hJ
    have a' := isCoef_coef g hw χ s' z J hJ
    rw [sval_lin g.b s s' c χ hJ]
    simp only [cst_eq, map_add, map_mul] at a a' ⊢
    linear_combination cstH z c * a + a'
  · intro w' hw'
    obtain ⟨c, hc, hv⟩ := exists_frame_ratio hw hw'
    refine ⟨c, hc, hv, fun s χ => coef_eq fun z J hJ => ?_⟩
    have a := isCoef_coef g hw χ s z J hJ
    rw [hv z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z c * a
  · intro t g₀ g' w' ht hadd hv s χ
    obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
    have a := isCoef_coef g hw χ s z J hJ
    have e := hs χ z J hJ
    rw [ht.1, _root_.mul_one] at hb
    have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
    rw [e₀, _root_.mul_one] at e
    have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
    rw [hv z J hJ, e, e₁, Units.val_mul, ht.2 χ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z (t (Multiplicative.ofAdd χ)).val * a

end GlobalTheory.UT.CoefBasic
end
