import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoord

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

/- English proof (translation)
Use `choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)`. Conclude with `⟨J, hJ⟩`.
-/
theorem exists_good' (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  exact ⟨J, hJ⟩

/- English proof (translation)
Take `⟨t, -, hv⟩` from `exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by`. Use `(Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)` and prove the remaining obligations. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]`. Rewrite using `[h U f, mul_inv_cancel])`. Use the proof step `(LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))`.

Establish `le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`. Use `⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Use `hv Z r z J hJ` as an intermediate fact. Rewrite `this` using `[val_mul hJ, val_inv, val_of t r z J PEmpty.elim (fun k => k.elim)]`. Establish `e` using `(gm_res r z le trivial (t.s PEmpty.elim)).trans this`.

Rewrite using `[e, inv_mul_cancel_right]`.
-/
theorem exists_ratio (hL : L.IsLB) (h : FormEq φ ε φ' ε') (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen)
    (u' : LB.Gen (LB.LinComb L φ' ε')) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [h U f, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of t r z J PEmpty.elim (fun k => k.elim)] at this
  have e := (gm_res r z le trivial (t.s PEmpty.elim)).trans this
  rw [e, inv_mul_cancel_right]

/- English proof (translation)
Establish `: u.s = u'.s` using `funext fun j => Units.ext (sec_ext_val hL (s := genSec u hu) (s' := genSec u' hu') (fun y J hJ => by rw [sval_genSec u hu _ y hJ, sval_genSec u' hu' _ y hJ, val_corr hJ h]) j)`. Consider the cases of `u`. Consider the cases of `u'`. Reduce the equality to equality of the corresponding arguments.
-/
theorem gen_eq_of_corr (hL : L.IsLB) {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : LB.Gen.Corr L φ ε φ ε u u') : u = u' := by
  have : u.s = u'.s := funext fun j => Units.ext (sec_ext_val hL (s := genSec u hu) (s' := genSec u' hu')
    (fun y J hJ => by rw [sval_genSec u hu _ y hJ, sval_genSec u' hu' _ y hJ, val_corr hJ h]) j)
  cases u; cases u'; congr

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_ratio hL h u hu u' hu'`. Establish `h1 : pullU π ⊤ a = 1` using `unit_ext fun z _ => by`. Take `⟨J, hJ⟩` from `exists_good' hL z`. Use `ha _ π z J hJ` as an intermediate fact. Rewrite `this` using `[hπ z J hJ]`.

Rewrite using `[gm_pull (𝟙 Y') π z ⊤ trivial, Category.id_comp, map_one]`. Conclude with `(mul_eq_right.1 this.symm)`. Establish `h2 : a = 1` using `Units.ext (GlobalTheory.FunDescent.app_injective π ⊤ ((congrArg Units.val h1).trans (map_one _).symm))`. Conclude with `corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]`.
-/
theorem corr_of_pull (hL : L.IsLB) (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen) {Y' : Scheme.{0}} (π : Y' ⟶ Y) [Flat π] [Surjective π]
    (hπ : ∀ z J, Good L z J → val u π z J = val u' π z J) : LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := exists_ratio hL h u hu u' hu'
  have h1 : pullU π ⊤ a = 1 := unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := ha _ π z J hJ
    rw [hπ z J hJ] at this
    rw [gm_pull (𝟙 Y') π z ⊤ trivial, Category.id_comp, map_one]
    exact (mul_eq_right.1 this.symm)
  have h2 : a = 1 := Units.ext (GlobalTheory.FunDescent.app_injective π ⊤
    ((congrArg Units.val h1).trans (map_one _).symm))
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]

end Gen

section Pts

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

def IsPointOf {T : Over (Spec (CommRingCat.of R))} (x : T.left ⟶ (thickObj R I e G).left) (ξ : GtPt D T) : Prop :=
  ξ.b.left = x ≫ g.pG.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (ξ.s χ) (LB.pullGen D.P.L _ _ (g.t χ) x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pG_left : g.pG.left = g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) := rfl

instance mono_thick : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/- English proof (translation)
Establish `e1 : lift τ y ≫ WeightPf.act g = (τ ≫ g.i) * y`. Establish `h1 : WeightPf.act g = (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) * snd _ _` using `rfl`. Rewrite using `[h1, MonObj.comp_mul, lift_fst_assoc, lift_snd]`. Establish `E1 : ((τ ≫ g.i) * y).left = (lift τ y).left ≫ (WeightPf.act g).left`. Rewrite using `[← Over.comp_left, e1]`.

Establish `E2 : y.left = (lift τ y).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left`. Rewrite using `[← Over.comp_left, lift_snd]`. Establish `E3 : τ.left = (lift τ y).left ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left`. Rewrite using `[← Over.comp_left, lift_fst]`. Establish `h` using `val_corr hJ (g.t_weight χ) (r ≫ (lift τ y).left)`.

Establish `h'` using `(val_pull hJ _ _ _).symm.trans (h.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))`. Establish `hc : val (charGen D.X (thickObj R I e G) D.P.L χ) (r ≫ (lift τ y).left) w J = gm r w ⊤ (splitTorusPointsEquiv _ D.X Z τ (Multiplicative.ofAdd χ))`. Establish `a : splitTorusPointsEquiv _ D.X Z τ (Multiplicative.ofAdd χ) = pullU τ.left ⊤ (charUnit _ D.X χ)` using `Units.ext (splitTorusPointsEquiv_val _ _ _ τ χ)`. Rewrite using `[a]`. Use `Eq.trans ?_ (gm_pull r τ.left w ⊤ trivial _).symm` and prove the remaining obligations.

Use `(gm_res _ w _ (hJ.mem PEmpty.elim _) _).trans ((gm_pull _ _ w ⊤ trivial _).trans ?_)` and prove the remaining obligations. Rewrite using `[E3, Category.assoc]`. Rewrite `h'` using `[hc]`. Rewrite using `[E1, ← Category.assoc]`. Use `conv_rhs => rw [E2, ← Category.assoc]`.

Conclude with `h'`.
-/
theorem val_t_act {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (χ : D.X) {W : Scheme.{0}} (r : W ⟶ Z.left) (w : W) (J)
    (hJ : Good D.P.L w J) :
    val (g.t χ) (r ≫ ((τ ≫ g.i) * y).left) w J =
      gm r w ⊤ (splitTorusPointsEquiv _ D.X Z τ (Multiplicative.ofAdd χ)) * val (g.t χ) (r ≫ y.left) w J := by
  have e1 : lift τ y ≫ WeightPf.act g = (τ ≫ g.i) * y := by
    have h1 : WeightPf.act g = (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) * snd _ _ := rfl
    rw [h1, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have E1 : ((τ ≫ g.i) * y).left = (lift τ y).left ≫ (WeightPf.act g).left := by
    rw [← Over.comp_left, e1]
  have E2 : y.left = (lift τ y).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left := by
    rw [← Over.comp_left, lift_snd]
  have E3 : τ.left = (lift τ y).left ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left := by
    rw [← Over.comp_left, lift_fst]
  have h := val_corr hJ (g.t_weight χ) (r ≫ (lift τ y).left)
  have h' := (val_pull hJ _ _ _).symm.trans (h.trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
  have hc : val (charGen D.X (thickObj R I e G) D.P.L χ) (r ≫ (lift τ y).left) w J =
      gm r w ⊤ (splitTorusPointsEquiv _ D.X Z τ (Multiplicative.ofAdd χ)) := by
    have a : splitTorusPointsEquiv _ D.X Z τ (Multiplicative.ofAdd χ) = pullU τ.left ⊤ (charUnit _ D.X χ) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ τ χ)
    rw [a]
    refine Eq.trans ?_ (gm_pull r τ.left w ⊤ trivial _).symm
    refine (gm_res _ w _ (hJ.mem PEmpty.elim _) _).trans ((gm_pull _ _ w ⊤ trivial _).trans ?_)
    rw [E3, Category.assoc]
  rw [hc] at h'
  rw [E1, ← Category.assoc]
  conv_rhs => rw [E2, ← Category.assoc]
  exact h'

/- English proof (translation)
Establish `hq : x ≫ g.q.left = y ≫ g.q.left`. Rewrite using `[← cancel_mono (pullback.fst D.P.A.hom (thick R I e)), Category.assoc, Category.assoc]`. Conclude with `hp`. Establish `hw : x ≫ (thickObj R I e G).hom = y ≫ (thickObj R I e G).hom`. Rewrite using `[← Over.w g.q, ← Category.assoc, hq, Category.assoc]`.

Set `FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))` to `Over.mk (y ≫ (thickObj R I e G).hom)`. Set `z1 : FinalForm ⟶ thickObj R I e G` to `Over.homMk x hw`. Set `z2 : FinalForm ⟶ thickObj R I e G` to `Over.homMk y rfl`. Establish `hq' : z1 ≫ g.q = z2 ≫ g.q` using `Over.OverMorphism.ext (by simpa [z1, z2] using hq)`. Use `g.q_hom` as an intermediate fact.

Use `g.i_hom` as an intermediate fact. Establish `hinv : z2⁻¹ ≫ g.q = (z2 ≫ g.q)⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]`. Establish `hd : (z1 * z2⁻¹) ≫ g.q = toUnit FinalForm ≫ η[thickObj R I e D.P.A]`.

Rewrite using `[MonObj.mul_comp, hinv, hq', mul_inv_cancel, Hom.one_def]`. Set `τ` to `g.isKernel.lift (z1 * z2⁻¹) (toUnit FinalForm) hd`. Establish `hτ : τ ≫ g.i = z1 * z2⁻¹` using `g.isKernel.lift_fst _ _ _`. Establish `e1 : (τ ≫ g.i) * z2 = z1` using `by rw [hτ, inv_mul_cancel_right]`. Establish `h1 : splitTorusPointsEquiv _ D.X FinalForm τ = 1`.

Use `MonoidHom.ext fun χ => unit_ext fun w _ => ?_` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB w`. Use `val_t_act g τ z2 (Multiplicative.toAdd χ) (𝟙 _) w J hJ` as an intermediate fact. Rewrite `this` using `[e1, Category.id_comp, Category.id_comp]`. Establish `h2` using `(ht _ w J hJ).symm.trans this`.

Rewrite using `[MonoidHom.one_apply, map_one]`. Conclude with `mul_eq_right.1 h2.symm`. Establish `h2 : τ = 1` using `(splitTorusPointsEquiv _ D.X FinalForm).injective (h1.trans (map_one _).symm)`. Rewrite `e1` using `[h2, MonObj.one_comp, _root_.one_mul]`. Conclude with `(congrArg (·.left) e1).symm`.
-/
theorem ext_of_val {W : Scheme.{0}} (x y : W ⟶ (thickObj R I e G).left) (hp : x ≫ g.pG.left = y ≫ g.pG.left)
    (ht : ∀ χ w J, Good D.P.L w J → val (g.t χ) x w J = val (g.t χ) y w J) : x = y := by
  have hq : x ≫ g.q.left = y ≫ g.q.left := by
    rw [← cancel_mono (pullback.fst D.P.A.hom (thick R I e)), Category.assoc, Category.assoc]
    exact hp
  have hw : x ≫ (thickObj R I e G).hom = y ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, ← Category.assoc, hq, Category.assoc]
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let z1 : FinalForm ⟶ thickObj R I e G := Over.homMk x hw
  let z2 : FinalForm ⟶ thickObj R I e G := Over.homMk y rfl
  have hq' : z1 ≫ g.q = z2 ≫ g.q := Over.OverMorphism.ext (by simpa [z1, z2] using hq)
  have := g.q_hom
  have := g.i_hom
  have hinv : z2⁻¹ ≫ g.q = (z2 ≫ g.q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hd : (z1 * z2⁻¹) ≫ g.q = toUnit FinalForm ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, hinv, hq', mul_inv_cancel, Hom.one_def]
  let τ := g.isKernel.lift (z1 * z2⁻¹) (toUnit FinalForm) hd
  have hτ : τ ≫ g.i = z1 * z2⁻¹ := g.isKernel.lift_fst _ _ _
  have e1 : (τ ≫ g.i) * z2 = z1 := by rw [hτ, inv_mul_cancel_right]
  have h1 : splitTorusPointsEquiv _ D.X FinalForm τ = 1 := by
    refine MonoidHom.ext fun χ => unit_ext fun w _ => ?_
    obtain ⟨J, hJ⟩ := exists_good' D.P.isLB w
    have := val_t_act g τ z2 (Multiplicative.toAdd χ) (𝟙 _) w J hJ
    rw [e1, Category.id_comp, Category.id_comp] at this
    have h2 := (ht _ w J hJ).symm.trans this
    rw [MonoidHom.one_apply, map_one]
    exact mul_eq_right.1 h2.symm
  have h2 : τ = 1 := (splitTorusPointsEquiv _ D.X FinalForm).injective (h1.trans (map_one _).symm)
  rw [h2, MonObj.one_comp, _root_.one_mul] at e1
  exact (congrArg (·.left) e1).symm

/- English proof (translation)
Establish `: padd D.P.A (DegPre.cT D T χ) b = padd D.P.A b (toUnit T ≫ D.c χ)` using `mul_comm (DegPre.cT D T χ) b`. Rewrite using `[DegPre.gtφT, this]`. Both sides reduce to the same expression.
-/
theorem gtφT_eq {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    DegPre.gtφT D T b χ = D.Oφ b χ := by
  have : padd D.P.A (DegPre.cT D T χ) b = padd D.P.A b (toUnit T ≫ D.c χ) :=
    mul_comm (DegPre.cT D T χ) b
  rw [DegPre.gtφT, this]; rfl

/- English proof (translation)
Establish `hw : x ≫ T'.hom = π ≫ T.hom`. Rewrite using `[← Over.w b, ← Over.w b', ← Category.assoc, ← h, Category.assoc]`. Set `Wo : Over (Spec (CommRingCat.of R))` to `Over.mk (π ≫ T.hom)`. Set `π' : Wo ⟶ T` to `Over.homMk π rfl`. Set `x' : Wo ⟶ T'` to `Over.homMk x hw`.

Establish `h' : π' ≫ b = x' ≫ b'` using `Over.OverMorphism.ext h`. Use `⟨fun χ k => ?_, fun χ χ' => ?_⟩` and prove the remaining obligations. Rewrite using `[gtφT_eq]`. Conclude with `(WeightPf.Oφ_comp π' b χ k).trans (h' ▸ (WeightPf.Oφ_comp x' b' χ k).symm)`. Establish `: π' ≫ lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b) = x' ≫ lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') b')`.

Simplify using `only [comp_lift, comp_toUnit_assoc, h']`. Conclude with `congrArg (·.left) this`.
-/
theorem comp_eq_of_left {T T' : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) {W : Scheme.{0}}
    (π : W ⟶ T.left) (x : W ⟶ T'.left) (h : π ≫ b.left = x ≫ b'.left) :
    (∀ χ k, π ≫ DegPre.gtφT D T b χ k = x ≫ D.Oφ b' χ k) ∧ ∀ χ χ' : D.X,
      π ≫ (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left =
        x ≫ (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') b')).left := by
  have hw : x ≫ T'.hom = π ≫ T.hom := by
    rw [← Over.w b, ← Over.w b', ← Category.assoc, ← h, Category.assoc]
  let Wo : Over (Spec (CommRingCat.of R)) := Over.mk (π ≫ T.hom)
  let π' : Wo ⟶ T := Over.homMk π rfl
  let x' : Wo ⟶ T' := Over.homMk x hw
  have h' : π' ≫ b = x' ≫ b' := Over.OverMorphism.ext h
  refine ⟨fun χ k => ?_, fun χ χ' => ?_⟩
  · rw [gtφT_eq]
    exact (WeightPf.Oφ_comp π' b χ k).trans (h' ▸ (WeightPf.Oφ_comp x' b' χ k).symm)
  · have : π' ≫ lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b) =
        x' ≫ lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') b') := by
      simp only [comp_lift, comp_toUnit_assoc, h']
    exact congrArg (·.left) this

/- English proof (translation)
Introduce `_ _ f` and use `Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ Oinvε k) ((comp_eq_of_left b b' π x h).1 χ k)`.
-/
theorem formEq_of_left {T T' : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) {W : Scheme.{0}}
    (π : W ⟶ T.left) (x : W ⟶ T'.left) (h : π ≫ b.left = x ≫ b'.left) (χ : D.X) :
    FormEq (fun k => π ≫ DegPre.gtφT D T b χ k) DegPre.gtε (fun k => x ≫ D.Oφ b' χ k) Oinvε :=
  fun _ _ f => Finset.prod_congr rfl fun k _ =>
    congrArg (fun q => f q ^ Oinvε k) ((comp_eq_of_left b b' π x h).1 χ k)

/- English proof (translation)
Use `formEq_of_left b b' (𝟙 _) x ((Category.id_comp _).trans h) χ` as an intermediate fact. Simplify `this` using `only [Category.id_comp]`.
-/
theorem formEq_of_left' {T T' : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A)
    (x : T.left ⟶ T'.left) (h : b.left = x ≫ b'.left) (χ : D.X) :
    FormEq (DegPre.gtφT D T b χ) DegPre.gtε (fun k => x ≫ D.Oφ b' χ k) Oinvε := by
  have := formEq_of_left b b' (𝟙 _) x ((Category.id_comp _).trans h) χ
  simpa only [Category.id_comp] using this

abbrev cubVal {W : Scheme.{0}} (r : W ⟶ (G3 D.P.A).left) (w : W) (J : (W ⟶ D.P.A.left) → D.P.L.ι) :
    (W.presheaf.stalk w)ˣ :=
  val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t r w J

/- English proof (translation)
The claim follows from `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans ((val_corr hJ (g.t_mul χ χ') x).trans (val_mul hJ _ _ _))`.
-/
theorem val_t_mul {W : Scheme.{0}} (x : W ⟶ (thickObj R I e G).left) (χ χ' : D.X) (w : W) (J)
    (hJ : Good D.P.L w J) :
    val (g.t (χ + χ')) x w J *
        cubVal (x ≫ (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') g.pG)).left) w J =
      val (g.t χ) x w J * val (g.t χ') x w J :=
  ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ (g.t_mul χ χ') x).trans (val_mul hJ _ _ _))

/- English proof (translation)
The claim follows from `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans ((val_corr hJ (ξ.mult χ χ') π).trans (val_mul hJ _ _ _))`.
-/
theorem val_s_mul {T : Over (Spec (CommRingCat.of R))} (ξ : GtPt D T) {W : Scheme.{0}} (π : W ⟶ T.left)
    (χ χ' : D.X) (w : W) (J) (hJ : Good D.P.L w J) :
    val (ξ.s (χ + χ')) π w J *
        cubVal (π ≫ (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') ξ.b)).left) w J =
      val (ξ.s χ) π w J * val (ξ.s χ') π w J :=
  ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ (ξ.mult χ χ') π).trans (val_mul hJ _ _ _))

/- English proof (translation)
Set `x' : T ⟶ (Over.map (thick R I e)).obj (thickObj R I e G)` to `Over.homMk x hx`. Set `b : T ⟶ D.P.A` to `x' ≫ g.pG`. Establish `hb : b.left = x ≫ g.pG.left` using `rfl`. Use `choose s hs vs using fun χ => exists_gen D.P.isLB (fun U _ f => (formEq_of_left' b g.pG x hb χ U f).symm) (LB.pullGen D.P.L _ _ (g.t χ) x) (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _)`. Establish `vs' : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = val (g.t χ) x y J` using `fun χ y J hJ => by`.

Rewrite using `[vs χ _ _ y J hJ, val_pull hJ, Category.id_comp]`. Establish `hm : ∀ χ χ' y J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J * cubVal (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left y J = val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J` using `fun χ χ' y J hJ => by`. Use `(comp_eq_of_left b g.pG (𝟙 _) x ((Category.id_comp _).trans hb)).2 χ χ'` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Rewrite using `[vs' _ y J hJ, vs' _ y J hJ, vs' _ y J hJ, this]`.

Conclude with `val_t_mul g x χ χ' y J hJ`. Use `⟨⟨b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, hb, fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩` and prove the remaining obligations. Establish `h` using `hm 0 0 y J hJ`. Establish `c0 : DegPre.cT D T 0 = 1` using `cPoint_zero T`. Establish `c1 : cubVal (lift (DegPre.cT D T 0) (lift (DegPre.cT D T 0) b)).left y J = 1`.

Rewrite using `[c0]`. Conclude with `(isCub_cubV D.cub hJ).face 1 b`. Rewrite `h` using `[c1, add_zero, _root_.mul_one]`. Conclude with `(mul_eq_left.1 h.symm).trans (val_one _).symm`. Use `(val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)` and prove the remaining obligations.

Use `Eq.trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_)) (hm χ χ' y J hJ)` and prove the remaining obligations. Rewrite using `[Category.id_comp]`.
-/
theorem exists_isPointOf {T : Over (Spec (CommRingCat.of R))} (x : T.left ⟶ (thickObj R I e G).left)
    (hx : x ≫ (thickObj R I e G).hom ≫ thick R I e = T.hom) : ∃ ξ : GtPt D T, IsPointOf g x ξ := by
  let x' : T ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x hx
  let b : T ⟶ D.P.A := x' ≫ g.pG
  have hb : b.left = x ≫ g.pG.left := rfl
  choose s hs vs using fun χ => exists_gen D.P.isLB
    (fun U _ f => (formEq_of_left' b g.pG x hb χ U f).symm) (LB.pullGen D.P.L _ _ (g.t χ) x)
    (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _)
  have vs' : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = val (g.t χ) x y J := fun χ y J hJ => by
    rw [vs χ _ _ y J hJ, val_pull hJ, Category.id_comp]
  have hm : ∀ χ χ' y J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J *
      cubVal (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left y J =
        val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J := fun χ χ' y J hJ => by
    have := (comp_eq_of_left b g.pG (𝟙 _) x ((Category.id_comp _).trans hb)).2 χ χ'
    rw [Category.id_comp] at this
    rw [vs' _ y J hJ, vs' _ y J hJ, vs' _ y J hJ, this]
    exact val_t_mul g x χ χ' y J hJ
  refine ⟨⟨b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩,
    hb, fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  · have h := hm 0 0 y J hJ
    have c0 : DegPre.cT D T 0 = 1 := cPoint_zero T
    have c1 : cubVal (lift (DegPre.cT D T 0) (lift (DegPre.cT D T 0) b)).left y J = 1 := by
      rw [c0]
      exact (isCub_cubV D.cub hJ).face 1 b
    rw [c1, add_zero, _root_.mul_one] at h
    exact (mul_eq_left.1 h.symm).trans (val_one _).symm
  · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine Eq.trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_)) (hm χ χ' y J hJ)
    rw [Category.id_comp]

/- English proof (translation)
Take `⟨b, s, hs, _, _⟩` from `ξ`. Take `⟨b', s', hs', _, _⟩` from `ξ'`. Take `rfl : b = b'` from `Over.OverMorphism.ext (h.1.trans h'.1.symm)`. Take `rfl : s = s'` from `funext fun χ => gen_eq_of_corr D.P.isLB (hs χ) (hs' χ) (DVR.corr_trans D.P.isLB (h.2 χ) (DVR.corr_symm (h'.2 χ)))`. Both sides reduce to the same expression.
-/
theorem IsPointOf.unique_right {T : Over (Spec (CommRingCat.of R))} {x : T.left ⟶ (thickObj R I e G).left}
    {ξ ξ' : GtPt D T} (h : IsPointOf g x ξ) (h' : IsPointOf g x ξ') : ξ = ξ' := by
  obtain ⟨b, s, hs, _, _⟩ := ξ
  obtain ⟨b', s', hs', _, _⟩ := ξ'
  obtain rfl : b = b' := Over.OverMorphism.ext (h.1.trans h'.1.symm)
  obtain rfl : s = s' := funext fun χ => gen_eq_of_corr D.P.isLB (hs χ) (hs' χ)
    (DVR.corr_trans D.P.isLB (h.2 χ) (DVR.corr_symm (h'.2 χ)))
  rfl

/- English proof (translation)
Use `ext_of_val g x x' (h.1.symm.trans h'.1) fun χ w J hJ => ?_` and prove the remaining obligations. Establish `a` using `(val_corr hJ (h.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)`. Establish `a'` using `(val_corr hJ (h'.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)`. Rewrite `a`, `a'` using `[Category.id_comp]`. Conclude with `a.symm.trans a'`.
-/
theorem IsPointOf.unique_left {T : Over (Spec (CommRingCat.of R))} {x x' : T.left ⟶ (thickObj R I e G).left}
    {ξ : GtPt D T} (h : IsPointOf g x ξ) (h' : IsPointOf g x' ξ) : x = x' := by
  refine ext_of_val g x x' (h.1.symm.trans h'.1) fun χ w J hJ => ?_
  have a := (val_corr hJ (h.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
  have a' := (val_corr hJ (h'.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
  rw [Category.id_comp] at a a'
  exact a.symm.trans a'

/- English proof (translation)
Use `choose a ha using fun χ => exists_ratio D.P.isLB (formEq_of_left ξ.b g.pG π y h χ) (LB.pullGen D.P.L _ _ (ξ.s χ) π) (DVR.pullGen_isGen _ _ _ _ (ξ.isGen χ) _) (LB.pullGen D.P.L _ _ (g.t χ) y) (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _)`. Establish `ha' : ∀ χ (V : Scheme.{0}) (r : V ⟶ W) (v : V) (J), Good D.P.L v J → val (ξ.s χ) (r ≫ π) v J = gm r v ⊤ (a χ) * val (g.t χ) (r ≫ y) v J` using `fun χ V r v J hJ => (val_pull hJ _ _ _).symm.trans ((ha χ V r v J hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))`. Establish `hm : ∀ χ χ', a (χ + χ') = a χ * a χ'` using `fun χ χ' => unit_ext fun w _ => by`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB w`. Establish `e1` using `val_s_mul ξ (𝟙 _ ≫ π) χ χ' w J hJ`.

Establish `e2` using `val_t_mul g (𝟙 _ ≫ y) χ χ' w J hJ`. Rewrite `e1` using `[ha' _ _ _ w J hJ, ha' _ _ _ w J hJ, ha' _ _ _ w J hJ, (comp_eq_of_left ξ.b g.pG (𝟙 _ ≫ π) (𝟙 _ ≫ y) (by rw [Category.id_comp, Category.id_comp, h])).2 χ χ', _root_.mul_assoc]`. Establish `e3` using `(congrArg (gm (𝟙 W) w ⊤ (a (χ + χ')) * ·) e2).symm.trans e1`. Rewrite `e3` using `[_root_.mul_mul_mul_comm]`. Rewrite using `[map_mul]`.

Conclude with `mul_right_cancel e3`. Set `FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))` to `Over.mk (y ≫ (thickObj R I e G).hom)`. Set `y' : FinalForm ⟶ thickObj R I e G` to `Over.homMk y rfl`. Set `u : Multiplicative D.X →* Γ(FinalForm.left, ⊤)ˣ` to `MonoidHom.mk' (fun χ => a χ.toAdd) fun χ χ' => hm _ _`. Set `τ` to `(splitTorusPointsEquiv _ D.X FinalForm).symm u`.

Use `g.q_hom` as an intermediate fact. Establish `hq : ((τ ≫ g.i) * y') ≫ g.q = y' ≫ g.q`. Rewrite using `[MonObj.mul_comp, Category.assoc, WeightPf.i_q, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]`. Use `⟨((τ ≫ g.i) * y').left, ?_, fun χ V r v J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[h, pG_left, ← Category.assoc, ← Category.assoc]`.

Conclude with `congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (thick R I e)) hq.symm`. Use `(ha' χ V r v J hJ).trans (Eq.trans ?_ (val_t_act g τ y' χ r v J hJ).symm)` and prove the remaining obligations. Rewrite using `[MulEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem exists_correction {T : Over (Spec (CommRingCat.of R))} (ξ : GtPt D T) {W : Scheme.{0}} (π : W ⟶ T.left)
    (y : W ⟶ (thickObj R I e G).left) (h : π ≫ ξ.b.left = y ≫ g.pG.left) :
    ∃ x : W ⟶ (thickObj R I e G).left, π ≫ ξ.b.left = x ≫ g.pG.left ∧
      ∀ χ (V : Scheme.{0}) (r : V ⟶ W) (v : V) (J), Good D.P.L v J →
        val (ξ.s χ) (r ≫ π) v J = val (g.t χ) (r ≫ x) v J := by
  choose a ha using fun χ => exists_ratio D.P.isLB (formEq_of_left ξ.b g.pG π y h χ)
    (LB.pullGen D.P.L _ _ (ξ.s χ) π) (DVR.pullGen_isGen _ _ _ _ (ξ.isGen χ) _)
    (LB.pullGen D.P.L _ _ (g.t χ) y) (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _)
  have ha' : ∀ χ (V : Scheme.{0}) (r : V ⟶ W) (v : V) (J), Good D.P.L v J →
      val (ξ.s χ) (r ≫ π) v J = gm r v ⊤ (a χ) * val (g.t χ) (r ≫ y) v J := fun χ V r v J hJ =>
    (val_pull hJ _ _ _).symm.trans ((ha χ V r v J hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  have hm : ∀ χ χ', a (χ + χ') = a χ * a χ' := fun χ χ' => unit_ext fun w _ => by
    obtain ⟨J, hJ⟩ := exists_good' D.P.isLB w
    have e1 := val_s_mul ξ (𝟙 _ ≫ π) χ χ' w J hJ
    have e2 := val_t_mul g (𝟙 _ ≫ y) χ χ' w J hJ
    rw [ha' _ _ _ w J hJ, ha' _ _ _ w J hJ, ha' _ _ _ w J hJ, (comp_eq_of_left ξ.b g.pG (𝟙 _ ≫ π) (𝟙 _ ≫ y)
      (by rw [Category.id_comp, Category.id_comp, h])).2 χ χ', _root_.mul_assoc] at e1
    have e3 := (congrArg (gm (𝟙 W) w ⊤ (a (χ + χ')) * ·) e2).symm.trans e1
    rw [_root_.mul_mul_mul_comm] at e3
    rw [map_mul]
    exact mul_right_cancel e3
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let y' : FinalForm ⟶ thickObj R I e G := Over.homMk y rfl
  let u : Multiplicative D.X →* Γ(FinalForm.left, ⊤)ˣ := MonoidHom.mk' (fun χ => a χ.toAdd) fun χ χ' => hm _ _
  let τ := (splitTorusPointsEquiv _ D.X FinalForm).symm u
  have := g.q_hom
  have hq : ((τ ≫ g.i) * y') ≫ g.q = y' ≫ g.q := by
    rw [MonObj.mul_comp, Category.assoc, WeightPf.i_q, ← Category.assoc, comp_toUnit, ← Hom.one_def,
      _root_.one_mul]
  refine ⟨((τ ≫ g.i) * y').left, ?_, fun χ V r v J hJ => ?_⟩
  · rw [h, pG_left, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (thick R I e)) hq.symm
  · refine (ha' χ V r v J hJ).trans (Eq.trans ?_ (val_t_act g τ y' χ r v J hJ).symm)
    rw [MulEquiv.apply_symm_apply]
    rfl

/- English proof (translation)
Use `g.q_flat` as an intermediate fact. Use `g.q_surj` as an intermediate fact. Use `g.q_affine` as an intermediate fact. Set `be : T.left ⟶ (thickObj R I e D.P.A).left` to `pullback.lift ξ.b.left σ ((Over.w ξ.b).trans hσ.symm)`. Establish `hbe : be ≫ pullback.fst D.P.A.hom (thick R I e) = ξ.b.left` using `pullback.lift_fst _ _ _`.

Set `π` to `pullback.snd g.q.left be`. Take `⟨x', hp, hv⟩` from `exists_correction g ξ π (pullback.fst g.q.left be) (by`. Rewrite using `[pG_left, pullback.condition_assoc, hbe])`. Establish `hd : ∀ {V : Scheme.{0}} (r r' : V ⟶ pullback g.q.left be), r ≫ π = r' ≫ π → r ≫ x' = r' ≫ x'` using `fun r r' h => ext_of_val g _ _ (by`. Rewrite using `[Category.assoc, Category.assoc, ← hp, ← Category.assoc, h, Category.assoc])`.

Use `fun χ w J hJ => by rw [← hv χ _ r w J hJ, ← hv χ _ r' w J hJ, h]`. Set `x` to `EffectiveEpi.desc π x' hd`. Establish `hx : π ≫ x = x'` using `EffectiveEpi.fac π x' hd`. Establish `hb : ξ.b.left = x ≫ g.pG.left`. Rewrite using `[← cancel_epi π, hp, ← Category.assoc, hx]`.

Use `⟨x, hb, fun χ => corr_of_pull D.P.isLB (formEq_of_left' ξ.b g.pG x hb χ) (ξ.isGen χ) (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) π fun z J hJ => ?_⟩` and prove the remaining obligations. Use `hv χ _ (𝟙 _) z J hJ` as an intermediate fact. Rewrite `this` using `[Category.id_comp, Category.id_comp, ← hx]`. Conclude with `this.trans (val_pull hJ _ _ _).symm`.
-/
theorem exists_point {T : Over (Spec (CommRingCat.of R))}
    (σ : T.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (hσ : σ ≫ thick R I e = T.hom) (ξ : GtPt D T) :
    ∃ x : T.left ⟶ (thickObj R I e G).left, IsPointOf g x ξ := by
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  let be : T.left ⟶ (thickObj R I e D.P.A).left := pullback.lift ξ.b.left σ ((Over.w ξ.b).trans hσ.symm)
  have hbe : be ≫ pullback.fst D.P.A.hom (thick R I e) = ξ.b.left := pullback.lift_fst _ _ _
  let π := pullback.snd g.q.left be
  obtain ⟨x', hp, hv⟩ := exists_correction g ξ π (pullback.fst g.q.left be) (by
    rw [pG_left, pullback.condition_assoc, hbe])
  have hd : ∀ {V : Scheme.{0}} (r r' : V ⟶ pullback g.q.left be), r ≫ π = r' ≫ π → r ≫ x' = r' ≫ x' :=
    fun r r' h => ext_of_val g _ _ (by
      rw [Category.assoc, Category.assoc, ← hp, ← Category.assoc, h, Category.assoc])
      fun χ w J hJ => by rw [← hv χ _ r w J hJ, ← hv χ _ r' w J hJ, h]
  let x := EffectiveEpi.desc π x' hd
  have hx : π ≫ x = x' := EffectiveEpi.fac π x' hd
  have hb : ξ.b.left = x ≫ g.pG.left := by
    rw [← cancel_epi π, hp, ← Category.assoc, hx]
  refine ⟨x, hb, fun χ => corr_of_pull D.P.isLB (formEq_of_left' ξ.b g.pG x hb χ) (ξ.isGen χ)
    (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) π fun z J hJ => ?_⟩
  have := hv χ _ (𝟙 _) z J hJ
  rw [Category.id_comp, Category.id_comp, ← hx] at this
  exact this.trans (val_pull hJ _ _ _).symm

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_point g σ hσ ξ`. Conclude with `⟨x, hx, fun x' hx' => hx'.unique_left g hx⟩`.
-/
theorem existsUnique_point {T : Over (Spec (CommRingCat.of R))}
    (σ : T.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (hσ : σ ≫ thick R I e = T.hom) (ξ : GtPt D T) :
    ∃! x : T.left ⟶ (thickObj R I e G).left, IsPointOf g x ξ := by
  obtain ⟨x, hx⟩ := exists_point g σ hσ ξ
  exact ⟨x, hx, fun x' hx' => hx'.unique_left g hx⟩

/- English proof (translation)
Rewrite using `[← Over.w ξ.b, h.1, Category.assoc, Over.w g.pG]`. Both sides reduce to the same expression.
-/
theorem IsPointOf.comp_hom {T : Over (Spec (CommRingCat.of R))} {x : T.left ⟶ (thickObj R I e G).left}
    {ξ : GtPt D T} (h : IsPointOf g x ξ) : x ≫ (thickObj R I e G).hom ≫ thick R I e = T.hom := by
  rw [← Over.w ξ.b, h.1, Category.assoc, Over.w g.pG]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [hf.1, h.1, Category.assoc], fun χ => DVR.corr_trans D.P.isLB (hf.2 χ) (DVR.corr_trans D.P.isLB (DVR.corr_pullGen (h.2 χ) f) (DVR.corr_pullGen_comp _ _ _))⟩`.
-/
theorem IsPointOf.pull {T T' : Over (Spec (CommRingCat.of R))} {x : T.left ⟶ (thickObj R I e G).left}
    {ξ : GtPt D T} {ξ' : GtPt D T'} (h : IsPointOf g x ξ) {f : T'.left ⟶ T.left} (hf : GtPt.IsPull f ξ ξ') :
    IsPointOf g (f ≫ x) ξ' :=
  ⟨by rw [hf.1, h.1, Category.assoc], fun χ => DVR.corr_trans D.P.isLB (hf.2 χ)
    (DVR.corr_trans D.P.isLB (DVR.corr_pullGen (h.2 χ) f) (DVR.corr_pullGen_comp _ _ _))⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [h'.1, h.1, Category.assoc], fun χ => DVR.corr_trans D.P.isLB (h'.2 χ) (DVR.corr_symm (DVR.corr_trans D.P.isLB (DVR.corr_pullGen (h.2 χ) f) (DVR.corr_pullGen_comp _ _ _)))⟩`.
-/
theorem IsPointOf.isPull {T T' : Over (Spec (CommRingCat.of R))} {x : T.left ⟶ (thickObj R I e G).left}
    {ξ : GtPt D T} {ξ' : GtPt D T'} (h : IsPointOf g x ξ) {f : T'.left ⟶ T.left} (h' : IsPointOf g (f ≫ x) ξ') :
    GtPt.IsPull f ξ ξ' :=
  ⟨by rw [h'.1, h.1, Category.assoc], fun χ => DVR.corr_trans D.P.isLB (h'.2 χ) (DVR.corr_symm
    (DVR.corr_trans D.P.isLB (DVR.corr_pullGen (h.2 χ) f) (DVR.corr_pullGen_comp _ _ _)))⟩

variable {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

def toGtPt (x : T ⟶ thickObj R I e G) : GtPt D ((Over.map (thick R I e)).obj T) :=
  (exists_isPointOf g (T := (Over.map (thick R I e)).obj T) x.left (by
    rw [← Category.assoc, Over.w x]; rfl)).choose

/- English proof (translation)
The claim follows from `(exists_isPointOf g (T := (Over.map (thick R I e)).obj T) x.left (by rw [← Category.assoc, Over.w x]; rfl)).choose_spec`.
-/
theorem isPointOf_toGtPt (x : T ⟶ thickObj R I e G) :
    IsPointOf g (T := (Over.map (thick R I e)).obj T) x.left (toGtPt g x) :=
  (exists_isPointOf g (T := (Over.map (thick R I e)).obj T) x.left (by
    rw [← Category.assoc, Over.w x]; rfl)).choose_spec

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (isPointOf_toGtPt g x).1`.
-/
theorem toGtPt_b (x : T ⟶ thickObj R I e G) : (toGtPt g x).b = (Over.map (thick R I e)).map x ≫ g.pG :=
  Over.OverMorphism.ext (isPointOf_toGtPt g x).1

/- English proof (translation)
The claim follows from `(isPointOf_toGtPt g x).2 χ`.
-/
theorem thickenedPointToTorusExtension_generator (x : T ⟶ thickObj R I e G) (χ : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ ((toGtPt g x).s χ) (LB.pullGen D.P.L _ _ (g.t χ) x.left) :=
  (isPointOf_toGtPt g x).2 χ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h ▸ isPointOf_toGtPt g x, fun h => (isPointOf_toGtPt g x).unique_right g h⟩`.
-/
theorem toGtPt_eq_iff (x : T ⟶ thickObj R I e G) (ξ : GtPt D ((Over.map (thick R I e)).obj T)) :
    toGtPt g x = ξ ↔ IsPointOf g (T := (Over.map (thick R I e)).obj T) x.left ξ :=
  ⟨fun h => h ▸ isPointOf_toGtPt g x, fun h => (isPointOf_toGtPt g x).unique_right g h⟩

/- English proof (translation)
Use `⟨fun x x' h => Over.OverMorphism.ext ((isPointOf_toGtPt g x).unique_left g (h ▸ isPointOf_toGtPt g x')), fun ξ => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `exists_point g (T := (Over.map (thick R I e)).obj T) T.hom rfl ξ`. Establish `hw : x ≫ (thickObj R I e G).hom = T.hom`. Rewrite using `[← cancel_mono (thick R I e), Category.assoc]`. Conclude with `hx.comp_hom g`.

Conclude with `⟨Over.homMk x hw, (toGtPt_eq_iff g _ ξ).2 hx⟩`.
-/
theorem toGtPt_bijective : Function.Bijective (toGtPt g (T := T)) := by
  refine ⟨fun x x' h => Over.OverMorphism.ext
    ((isPointOf_toGtPt g x).unique_left g (h ▸ isPointOf_toGtPt g x')), fun ξ => ?_⟩
  obtain ⟨x, hx⟩ := exists_point g (T := (Over.map (thick R I e)).obj T) T.hom rfl ξ
  have hw : x ≫ (thickObj R I e G).hom = T.hom := by
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact hx.comp_hom g
  exact ⟨Over.homMk x hw, (toGtPt_eq_iff g _ ξ).2 hx⟩

def pointsEquiv (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) ≃ GtPt D ((Over.map (thick R I e)).obj T) :=
  Equiv.ofBijective _ (toGtPt_bijective g)

end Pts

end GlobalTheory.TorusCoord
