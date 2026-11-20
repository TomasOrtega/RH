import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.FamVal
open ReciprocityTheory.ChartRestriction.G.DVR

section General
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
Rewrite using `[valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]`. Use `show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _`. Rewrite using `[Iso.hom_inv_id_apply]`. Conclude with `TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _`.
-/
theorem toStk_valF' (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) (a : Γ(X, U)) :
    toStk z (valF x U a) = gs x z U a := by
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

/- English proof (translation)
The claim follows from `toStk_valF' r _ z (hJ.mem φ r) _`.
-/
theorem toStk_sF {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) :
    toStk z (sF s r J) = sval s r z J := toStk_valF' r _ z (hJ.mem φ r) _

/- English proof (translation)
The claim follows from `toStk_valF r _ z (hJ.mem φ r) _`.
-/
theorem toStk_vF {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) :
    toStk z (vF t r J) = (val t r z J).val := toStk_valF r _ z (hJ.mem φ r) _

/- English proof (translation)
Establish `: JacobsonSpace Y` using `LocallyOfFiniteType.jacobsonSpace π`. Rewrite using `[← sub_eq_zero]`. Use `(basicOpen_eq_bot_iff _).1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hne' : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty`.

Rewrite using `[Set.nonempty_iff_ne_empty]`. Conclude with `fun e => hne (SetLike.coe_injective e)`. Take `⟨y, hy, hc⟩` from `nonempty_inter_closedPoints hne' (Y.basicOpen (a - b)).isOpen.isLocallyClosed`. Set `x : Sp F ⟶ Y` to `pointOfClosedPoint π y hc`. Establish `hb : x z ∈ Y.basicOpen (a - b)`.

Rewrite using `[pointOfClosedPoint_apply π y hc z]`. Conclude with `hy`. Establish `hU : x z ∈ U` using `Y.basicOpen_le _ hb`. Establish `e` using `h x (pointOfClosedPoint_comp π y hc) hU`. Rewrite `e` using `[gs_eq x z _ hU, gs_eq x z _ hU, ← sub_eq_zero, ← map_sub, ← map_sub]`.

Establish `hb' : z ∈ (Sp F).basicOpen ((x.app U).hom (a - b))`. Rewrite using `[← Scheme.preimage_basicOpen]`. Conclude with `hb`. Conclude with `(((Sp F).mem_basicOpen _ z hU).1 hb').ne_zero e`.
-/
theorem fn_ext_pts [IsAlgClosed F] [IsReduced Y] (π : Y ⟶ Sp F) [LocallyOfFiniteType π] (z : Sp F) (U : Y.Opens)
    (a b : Γ(Y, U)) (h : ∀ x : Sp F ⟶ Y, x ≫ π = 𝟙 _ → x z ∈ U → gs x z U a = gs x z U b) : a = b := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace π
  rw [← sub_eq_zero]
  refine (basicOpen_eq_bot_iff _).1 ?_
  by_contra hne
  have hne' : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (Y.basicOpen (a - b)).isOpen.isLocallyClosed
  let x : Sp F ⟶ Y := pointOfClosedPoint π y hc
  have hb : x z ∈ Y.basicOpen (a - b) := by
    rw [pointOfClosedPoint_apply π y hc z]
    exact hy
  have hU : x z ∈ U := Y.basicOpen_le _ hb
  have e := h x (pointOfClosedPoint_comp π y hc) hU
  rw [gs_eq x z _ hU, gs_eq x z _ hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  have hb' : z ∈ (Sp F).basicOpen ((x.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]
    exact hb
  exact (((Sp F).mem_basicOpen _ z hU).1 hb').ne_zero e

/- English proof (translation)
The claim follows from `fn_ext_pts π z (LB.wchart L φ j) _ _ fun x hx hU => (sec_trans s x z hU (hJ.mem φ x)).trans ((congrArg _ (h x hx)).trans (sec_trans s' x z hU (hJ.mem φ x)).symm)`.
-/
theorem sec_ext_pts [IsAlgClosed F] [IsReduced Y] (π : Y ⟶ Sp F) [LocallyOfFiniteType π] {z : Sp F}
    {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ x : Sp F ⟶ Y, x ≫ π = 𝟙 _ → sval s x z J = sval s' x z J) (j : K → L.ι) : s.f j = s'.f j :=
  fn_ext_pts π z (LB.wchart L φ j) _ _ fun x hx hU =>
    (sec_trans s x z hU (hJ.mem φ x)).trans ((congrArg _ (h x hx)).trans (sec_trans s' x z hU (hJ.mem φ x)).symm)

end General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

/- English proof (translation)
Introduce `ψ` and use `(top_le_iff_mem ψ _ z).1 (ν.good ψ)`.
-/
theorem good : Good D.P.L z ν.J := fun ψ => (top_le_iff_mem ψ _ z).1 (ν.good ψ)

abbrev pt (x : N.A) : TF (R := R) F ⟶ DegPre.BF D F := lift (𝟙 (TF (R := R) F)) (ν.eA x)

abbrev un : Fˣ →* ((Sp F).presheaf.stalk z)ˣ := Units.map (toStk z).toMonoidHom

/- English proof (translation)
The claim follows from `lift_fst _ _`.
-/
theorem pt_fst (x : N.A) : pt ν x ≫ fst _ _ = 𝟙 _ := lift_fst _ _

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, tr_fst, pt_fst, pt_fst]`. Rewrite using `[Category.assoc]`. Use `(congrArg _ (tr_pr D F _)).trans ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, ← Category.assoc, pt_fst, Category.id_comp, lift_snd, lift_snd, map_mul]`.
-/
theorem pt_tr (x b : N.A) : pt ν x ≫ DegPre.trPt D F (ν.eA b) = pt ν (x * b) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, pt_fst, pt_fst]
  · rw [Category.assoc]
    refine (congrArg _ (tr_pr D F _)).trans ?_
    rw [MonObj.comp_mul, ← Category.assoc, pt_fst, Category.id_comp, lift_snd, lift_snd, map_mul]

/- English proof (translation)
The claim follows from `(ν.c_eq α).symm`.
-/
theorem indicatorIdempotent_eq_add_sum (α : N.X) : cP D (TF (R := R) F) (ν.eX α) = ν.eA (N.c α) := (ν.c_eq α).symm

/- English proof (translation)
The claim follows from `Units.ext ((toStk_vF (good ν z) _ _).symm.trans (congrArg (toStk z) (ν.θ_eq x y u).symm))`.
-/
theorem th_eq (x y u : N.A) :
    th D (T := TF (R := R) F) z ν.J (ν.eA x) (ν.eA y) (ν.eA u) = un z (N.θ x y u) :=
  Units.ext ((toStk_vF (good ν z) _ _).symm.trans (congrArg (toStk z) (ν.θ_eq x y u).symm))

/- English proof (translation)
Rewrite using `[uVal, ← Category.assoc, pt_fst, Category.id_comp, lift_snd, indicatorIdempotent_eq_add_sum, th_eq, NumB.uV, map_div, div_eq_mul_inv, cubN, cubN, map_prod]`. Use `congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul, th_eq]`.
-/
theorem uVal_eq (k : ℕ) (α : N.X) (b x : N.A) :
    uVal D F k (ν.eX α) (ν.eA b) (pt ν x) z ν.J = un z (N.uV k (N.c α) b x) := by
  rw [uVal, ← Category.assoc, pt_fst, Category.id_comp, lift_snd, indicatorIdempotent_eq_add_sum, th_eq, NumB.uV, map_div, div_eq_mul_inv,
    cubN, cubN, map_prod]
  refine congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)
  rw [← map_pow, ← map_mul, th_eq]

abbrev rgU : ((Sp F).presheaf.stalk z)ˣ := val D.rigK (jFK (R := R) F) z ν.J

/- English proof (translation)
The claim follows from `(toStk_vF (good ν z) _ _).trans (congrArg Units.val (val_pull (good ν z) D.rig (toUnit (TK R)).left _).symm)`.
-/
theorem rg_eq : toStk z ν.rg = (rgU ν z).val :=
  (toStk_vF (good ν z) _ _).trans (congrArg Units.val (val_pull (good ν z) D.rig (toUnit (TK R)).left _).symm)

/- English proof (translation)
Introduce `h` and use `by let z : Sp F := IsLocalRing.closedPoint F have := rg_eq ν z rw [h, map_zero] at this exact (rgU ν z).ne_zero this.symm`.
-/
theorem rg_ne : ν.rg ≠ 0 := fun h => by
  let z : Sp F := IsLocalRing.closedPoint F
  have := rg_eq ν z
  rw [h, map_zero] at this
  exact (rgU ν z).ne_zero this.symm

/- English proof (translation)
The claim follows from `Units.ext ((congrArg (toStk z) (ν.ψ_eq α)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (toStk_vF (good ν z) _ _) (rg_eq ν z))))`.
-/
theorem psi_eq (α : N.X) : un z (N.ψ α) = val (D.psi (ν.eX α)) (jFK (R := R) F) z ν.J * rgU ν z :=
  Units.ext ((congrArg (toStk z) (ν.ψ_eq α)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF (good ν z) _ _) (rg_eq ν z))))

/- English proof (translation)
Establish `hJ` using `good ν z`. Establish `e : ∀ a b : D.X, val (D.tau a b) (jFK (R` using `R) F) z ν.J = val (D.psi (a + b)) (jFK (R := R) F) z ν.J * (val (D.psi a) (jFK (R := R) F) z ν.J)⁻¹ * (val (D.psi b) (jFK (R := R) F) z ν.J)⁻¹ * (rgU ν z)⁻¹ := fun a b => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _). …`. Establish `p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi (ν.eX mu)) k) (jFK (R` using `R) F) z ν.J = val (D.psi (ν.eX mu)) (jFK (R := R) F) z ν.J ^ k := map_pow _ _ _`. Establish `p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (jFK (R` using `R) F) z ν.J = rgU ν z ^ k := map_pow _ _ _`. Use `val_famMult (D := D) (𝟙 (TF (R := R) F)) hJ k (ν.eX mu) (ν.eX α)` as an intermediate fact.

Rewrite `this` using `[Over.id_left, Category.id_comp]`. Use `this.trans ?_` and prove the remaining obligations. Use `erw [p₁, p₂, e]`. Rewrite using `[NumD.τ, map_mul, map_pow, map_div, map_div, psi_eq ν, psi_eq ν, psi_eq ν, map_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_pow]`. Use `module`.
-/
theorem famMult_eq (k : ℕ) (mu α : N.X) :
    val (DegPre.famMult D F k (ν.eX mu) (ν.eX α)) (𝟙 (Sp F)) z ν.J = un z (N.ψ mu ^ k * N.τ mu α) := by
  have hJ := good ν z
  have e : ∀ a b : D.X, val (D.tau a b) (jFK (R := R) F) z ν.J =
      val (D.psi (a + b)) (jFK (R := R) F) z ν.J * (val (D.psi a) (jFK (R := R) F) z ν.J)⁻¹ *
        (val (D.psi b) (jFK (R := R) F) z ν.J)⁻¹ * (rgU ν z)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi (ν.eX mu)) k) (jFK (R := R) F) z ν.J =
      val (D.psi (ν.eX mu)) (jFK (R := R) F) z ν.J ^ k := map_pow _ _ _
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (jFK (R := R) F) z ν.J = rgU ν z ^ k := map_pow _ _ _
  have := val_famMult (D := D) (𝟙 (TF (R := R) F)) hJ k (ν.eX mu) (ν.eX α)
  rw [Over.id_left, Category.id_comp] at this
  refine this.trans ?_
  erw [p₁, p₂, e]
  rw [NumD.τ, map_mul, map_pow, map_div, map_div, psi_eq ν, psi_eq ν, psi_eq ν, map_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_pow]
  module

/- English proof (translation)
Use `forall₂_congr fun α x => ?_` and prove the remaining obligations. Rewrite using `[← toStk_sF (good ν z), Units.val_pow_eq_pow_val, ← rg_eq, ← map_pow, ← map_mul]`. Conclude with `(toStk z).injective.eq_iff.symm`.
-/
theorem famV_iff {k : ℕ} (s : Fam D F k) (f : N.X → N.A → F) : ν.FamV s f ↔
    ∀ α x, toStk z (f α x) * (rgU ν z ^ k).val = sval (s.s (ν.eX α)) (pt ν x).left z ν.J := by
  refine forall₂_congr fun α x => ?_
  rw [← toStk_sF (good ν z), Units.val_pow_eq_pow_val, ← rg_eq, ← map_pow, ← map_mul]
  exact (toStk z).injective.eq_iff.symm

/- English proof (translation)
Establish `h` using `pow_ne_zero k (rg_ne ν)`. Use `⟨fun α x => sF (s.s (ν.eX α)) (pt ν x).left ν.J / ν.rg ^ k, fun α x => div_mul_cancel₀ _ h, fun f hf => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `α x`. Conclude with `eq_div_of_mul_eq h (hf α x)`.
-/
theorem exists_famV {k : ℕ} (s : Fam D F k) : ∃! f, ν.FamV s f := by
  have h := pow_ne_zero k (rg_ne ν)
  refine ⟨fun α x => sF (s.s (ν.eX α)) (pt ν x).left ν.J / ν.rg ^ k, fun α x => div_mul_cancel₀ _ h, fun f hf => ?_⟩
  funext α x
  exact eq_div_of_mul_eq h (hf α x)

/- English proof (translation)
Set `ρ : TF (R` to `R) F ⟶ DegPre.BF D F := Over.homMk r (by`. Rewrite using `[← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc]`. Conclude with `(congrArg (· ≫ _) hr).trans (Category.id_comp _))`. Use `⟨ν.eA.symm (ρ ≫ snd _ _), congrArg (fun q : TF (R := R) F ⟶ DegPre.BF D F => q.left) (?_ : ρ = _)⟩` and prove the remaining obligations. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Rewrite using `[pt_fst]`. Conclude with `Over.OverMorphism.ext hr`. Rewrite using `[lift_snd, MulEquiv.apply_symm_apply]`.
-/
theorem exists_pt (r : Sp F ⟶ (DegPre.BF D F).left) (hr : r ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _) :
    ∃ x, r = (pt ν x).left := by
  let ρ : TF (R := R) F ⟶ DegPre.BF D F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc]
    exact (congrArg (· ≫ _) hr).trans (Category.id_comp _))
  refine ⟨ν.eA.symm (ρ ≫ snd _ _), congrArg (fun q : TF (R := R) F ⟶ DegPre.BF D F => q.left) (?_ : ρ = _)⟩
  apply CartesianMonoidalCategory.hom_ext
  · rw [pt_fst]; exact Over.OverMorphism.ext hr
  · rw [lift_snd, MulEquiv.apply_symm_apply]

/- English proof (translation)
Set `z : Sp F` to `IsLocalRing.closedPoint F`. Set `π : (DegPre.BF D F).left ⟶ Sp F` to `(fst (TF (R := R) F) D.P.A).left`. Use `D.P.isAb.smooth` as an intermediate fact. Establish `: Smooth π` using `inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.P.A.hom))`. Establish `: IsReduced (DegPre.BF D F).left` using `GlobalTheory.isReduced_of_smooth_of_isReduced π`.

Use `fam_ext fun α j => ?_` and prove the remaining obligations. Take `⟨α, rfl⟩` from `ν.eX.surjective α`. Use `sec_ext_pts π (good ν z) (fun r hr => ?_) j` and prove the remaining obligations. Take `⟨x, rfl⟩` from `exists_pt ν r hr`. Conclude with `((famV_iff ν z s f).1 h α x).symm.trans ((famV_iff ν z s' f).1 h' α x)`.
-/
theorem famV_inj [IsAlgClosed F] {k : ℕ} {s s' : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f) (h' : ν.FamV s' f) :
    s = s' := by
  let z : Sp F := IsLocalRing.closedPoint F
  let π : (DegPre.BF D F).left ⟶ Sp F := (fst (TF (R := R) F) D.P.A).left
  have := D.P.isAb.smooth
  have : Smooth π := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsReduced (DegPre.BF D F).left := GlobalTheory.isReduced_of_smooth_of_isReduced π
  refine fam_ext fun α j => ?_
  obtain ⟨α, rfl⟩ := ν.eX.surjective α
  refine sec_ext_pts π (good ν z) (fun r hr => ?_) j
  obtain ⟨x, rfl⟩ := exists_pt ν r hr
  exact ((famV_iff ν z s f).1 h α x).symm.trans ((famV_iff ν z s' f).1 h' α x)

/- English proof (translation)
Introduce `mu α x`. Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ` using `good ν z`. Establish `H` using `(famV_iff ν z s f).1 h`. Take `⟨⟨u, hu, hc⟩, hv⟩` from `gen_fe (D := D) (F := F) hG k (ν.eX mu) (ν.eX α)`.

Establish `e` using `(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe _ _ u hu hc) _ (pt ν x).left z ν.J hJ`. Rewrite `e` using `[hv u hu hc _ (pt ν x) z ν.J hJ, trF_eq, ← Over.comp_left, indicatorIdempotent_eq_add_sum, pt_tr, uVal_eq, pt_fst, ← H]`. Establish `e₁` using `H (α + k • mu) x`. Rewrite `e₁` using `[map_add, map_nsmul, e]`. Establish `e₂` using `famMult_eq ν z k mu α`.

Use `(toStk z).injective ((Units.mul_left_inj (rgU ν z ^ k)).1 (e₁.trans ?_))` and prove the remaining obligations. Use `erw [e₂]`. Rewrite using `[← map_mul, ← _root_.mul_assoc, map_mul (toStk z)]`. Express the relevant statement in the definitionally equal form `_ * _ * toStk z _ = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem famV_fe (hG : GlobalFnsSt) {k : ℕ} {s : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f) : N.FE k f := by
  intro mu α x
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have H := (famV_iff ν z s f).1 h
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k (ν.eX mu) (ν.eX α)
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe _ _ u hu hc) _ (pt ν x).left z ν.J hJ
  rw [hv u hu hc _ (pt ν x) z ν.J hJ, trF_eq, ← Over.comp_left, indicatorIdempotent_eq_add_sum, pt_tr, uVal_eq, pt_fst, ← H] at e
  have e₁ := H (α + k • mu) x
  rw [map_add, map_nsmul, e] at e₁
  have e₂ := famMult_eq ν z k mu α
  refine (toStk z).injective ((Units.mul_left_inj (rgU ν z ^ k)).1 (e₁.trans ?_))
  erw [e₂]
  rw [← map_mul, ← _root_.mul_assoc, map_mul (toStk z)]
  change _ * _ * toStk z _ = _
  ring

/- English proof (translation)
Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ` using `good ν z`. Establish `H` using `(famV_iff ν z s f).1 h`. Take `⟨h₁, h₂, h₃⟩` from `hp`. Use `(famV_iff ν z t _).2 fun α x => ?_` and prove the remaining obligations.

Establish `e` using `ht (ν.eX (α - q.1.1.toAdd)) (ν.eX α) (by rw [← h₁, ← map_add, sub_add_cancel]) _ (pt ν x) z ν.J hJ`. Establish `e₁ : uVal D F k (ν.eX (α - q.1.1.toAdd)) p.g.b (pt ν x) z ν.J = _` using `h₂ ▸ uVal_eq ν z k _ q.1.2.b x`. Establish `e₂ : pt ν x ≫ DegPre.trPt D F p.g.b = pt ν (x * q.1.2.b)` using `h₂ ▸ pt_tr ν x q.1.2.b`. Establish `e₃ : (val (LB.mulGen D.P.L _ _ _ _ (p.g.s (ν.eX (α - q.1.1.toAdd))) w) (𝟙 (Sp F)) z ν.J).val = toStk z (q.1.2.s (α - q.1.1.toAdd)) * toStk z wv`. Rewrite using `[h₃, hw, toStk_vF hJ, toStk_vF hJ]`.

Conclude with `congrArg Units.val (val_mul hJ _ _ _)`. Rewrite `e` using `[e₁, e₂, pt_fst, ← H, Units.val_mul]`. Use `Eq.trans ?_ e.symm` and prove the remaining obligations. Use `erw [e₃]`. Rewrite using `[NumD.phi, map_mul (toStk z), Units.val_mul, Units.val_mul, map_mul (toStk z), map_mul (toStk z)]`.

Express the relevant statement in the definitionally equal form `_ = _ * _ * (toStk z _ * _)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiVal_famV {k : ℕ} {p : QkPt D F k} {q : N.QT k} (hp : ν.QPt p q)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))} {wv : Fˣ}
    (hw : (wv : F) = vF w (𝟙 (Sp F)) ν.J) {s t : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f)
    (ht : PhiVal p w s.s t.s) : ν.FamV t (N.phi q wv f) := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have H := (famV_iff ν z s f).1 h
  obtain ⟨h₁, h₂, h₃⟩ := hp
  refine (famV_iff ν z t _).2 fun α x => ?_
  have e := ht (ν.eX (α - q.1.1.toAdd)) (ν.eX α) (by rw [← h₁, ← map_add, sub_add_cancel]) _ (pt ν x) z ν.J hJ
  have e₁ : uVal D F k (ν.eX (α - q.1.1.toAdd)) p.g.b (pt ν x) z ν.J = _ := h₂ ▸ uVal_eq ν z k _ q.1.2.b x
  have e₂ : pt ν x ≫ DegPre.trPt D F p.g.b = pt ν (x * q.1.2.b) := h₂ ▸ pt_tr ν x q.1.2.b
  have e₃ : (val (LB.mulGen D.P.L _ _ _ _ (p.g.s (ν.eX (α - q.1.1.toAdd))) w) (𝟙 (Sp F)) z ν.J).val =
      toStk z (q.1.2.s (α - q.1.1.toAdd)) * toStk z wv := by
    rw [h₃, hw, toStk_vF hJ, toStk_vF hJ]
    exact congrArg Units.val (val_mul hJ _ _ _)
  rw [e₁, e₂, pt_fst, ← H, Units.val_mul] at e
  refine Eq.trans ?_ e.symm
  erw [e₃]
  rw [NumD.phi, map_mul (toStk z), Units.val_mul, Units.val_mul, map_mul (toStk z), map_mul (toStk z)]
  change _ = _ * _ * (toStk z _ * _)
  ring

omit ν z in
/- English proof (translation)
The claim follows from `(congrArg (gs r z _) (h _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl))`.
-/
theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s t : LB.Sec (LB.LinComb L φ ε)} {c : Γ(Y, ⊤)} (h : ∀ j, s.f j = resTop _ c * t.f j) (r : Z ⟶ Y) {z : Z} {J}
    (hJ : Good L z J) : sval s r z J = gs r z ⊤ c * sval t r z J :=
  (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl))

omit ν z in

/- English proof (translation)
Introduce `s`. Set `i : P.A ⟶ baseOver (Sp R) ⊗ P.A` to `lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)`. Establish `w : (snd (baseOver (Sp R)) P.A).left ≫ P.A.hom = (fst (baseOver (Sp R)) P.A).left` using `(Over.w (snd (baseOver (Sp R)) P.A)).trans ((Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _))`. Establish `hi : i.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _` using `congrArg (fun q : P.A ⟶ P.A => q.left) (lift_snd _ _)`. Establish `hi' : snd (baseOver (Sp R)) P.A ≫ i = 𝟙 _`.

Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, lift_fst, Category.id_comp]`. Conclude with `Over.OverMorphism.ext w`. Rewrite using `[Category.assoc, lift_snd, Category.id_comp, Category.comp_id]`. Take `⟨r, hr⟩` from `ht (VVRank.pullTo (φ := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) (φ' := fun _ => 𝟙 _) s i.left fun _ => hi)`.

Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, fun j => ?_⟩` and prove the remaining obligations. Use `sec_ext_val (s' := SecOps.secScale ((fst (baseOver (Sp R)) P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) t (snd (baseOver (Sp R)) P.A).left fun _ => Category.comp_id _)) P.isLB (fun …` and prove the remaining obligations. Establish `e` using `sval_scale hr (snd (baseOver (Sp R)) P.A).left hJ`. Use `replace e := (VVRank.sval_pullTo _ _ _ _ _ hJ).symm.trans e`. Rewrite `e` using `[← Over.comp_left, hi']`.

Use `e.trans (Eq.trans ?_ (sval_scale (fun _ => rfl) _ hJ).symm)` and prove the remaining obligations. Use `congrArg₂ (· * ·) ((gs_pull _ P.A.hom y ⊤ trivial _).trans (Eq.trans ?_ (gs_pull _ _ y ⊤ trivial _).symm)) (Eq.trans ?_ (VVRank.sval_pullTo _ _ _ _ _ hJ).symm)` and prove the remaining obligations. Rewrite using `[w, Category.id_comp]`. Rewrite using `[Category.id_comp]`.
-/
theorem isGenSec_base (P : PolAV (Sp R)) (t : H0 P.L 1)
    (ht : ∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * t.f j) :
    IsGenSec P.A P.L 1 (T := baseOver (Sp R)) (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left)
      t (snd (baseOver (Sp R)) P.A).left fun _ => Category.comp_id _) := by
  intro s
  let i : P.A ⟶ baseOver (Sp R) ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have w : (snd (baseOver (Sp R)) P.A).left ≫ P.A.hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (snd (baseOver (Sp R)) P.A)).trans ((Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _))
  have hi : i.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _ := congrArg (fun q : P.A ⟶ P.A => q.left) (lift_snd _ _)
  have hi' : snd (baseOver (Sp R)) P.A ≫ i = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      exact Over.OverMorphism.ext w
    · rw [Category.assoc, lift_snd, Category.id_comp, Category.comp_id]
  obtain ⟨r, hr⟩ := ht (VVRank.pullTo (φ := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) (φ' := fun _ => 𝟙 _)
    s i.left fun _ => hi)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, fun j => ?_⟩
  refine sec_ext_val (s' := SecOps.secScale ((fst (baseOver (Sp R)) P.A).left.appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) (VVRank.pullTo
      (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left)
      t (snd (baseOver (Sp R)) P.A).left fun _ => Category.comp_id _)) P.isLB (fun y J hJ => ?_) j
  have e := sval_scale hr (snd (baseOver (Sp R)) P.A).left hJ
  replace e := (VVRank.sval_pullTo _ _ _ _ _ hJ).symm.trans e
  rw [← Over.comp_left, hi'] at e
  refine e.trans (Eq.trans ?_ (sval_scale (fun _ => rfl) _ hJ).symm)
  refine congrArg₂ (· * ·) ((gs_pull _ P.A.hom y ⊤ trivial _).trans (Eq.trans ?_ (gs_pull _ _ y ⊤ trivial _).symm))
    (Eq.trans ?_ (VVRank.sval_pullTo _ _ _ _ _ hJ).symm)
  · rw [w, Category.id_comp]
  · rw [Category.id_comp]

/- English proof (translation)
Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ` using `good ν z`. Establish `H` using `(famV_iff ν z s f).1 h`. Set `b : TF (R` to `R) F ⟶ baseOver (Sp R) := Over.homMk (TF (R := R) F).hom (Category.comp_id _)`. Establish `: IsAffine (TF (R` using `R) F).left := inferInstanceAs (IsAffine (Sp F))`.

Establish `: IsAffine (baseOver (Sp R)).left` using `inferInstanceAs (IsAffine (Sp R))`. Establish `hg` using `EmbPull.isGenSec_pullS D.P hS b (isGenSec_base D.P ν.th ν.th_gen)`. Take `⟨σ, hσ⟩` from `exists_sec D.P.isLB (φ' := fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ε' := fun _ => (1 : ℤ)) (fun U _ g => by`. Establish `p` using `prod_fam D F (𝟙 _) (ν.eX 0) 1 g`. Establish `c₀ : cP D (DegPre.BF D F) (ν.eX 0) = 1`.

Use `cPoint_nsmul D (DegPre.BF D F) 0 (ν.eX 0)` as an intermediate fact. Rewrite `this` using `[zero_nsmul, pow_zero, ← map_zero ν.eX]`. Then use the resulting hypothesis. Simplify using `only [Over.id_left, Category.id_comp] at p`. Rewrite using `[p, c₀, _root_.one_mul, Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, inv_mul_cancel_right, Fintype.prod_unique, zpow_one]) (s.s (ν.eX 0))`. Take `⟨r, hr⟩` from `hg σ`.

Use `⟨valF (𝟙 (Sp F)) ⊤ r, fun x => ?_⟩` and prove the remaining obligations. Establish `e` using `sval_scale (φ := fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ε := fun _ => (1 : ℤ)) (c := (fst (TF (R := R) F) D.P.A).left.appTop.hom r) hr (pt ν x).left hJ`. Establish `e₁ : gs (pt ν x).left z ⊤ ((fst (TF (R` using `R) F) D.P.A).left.appTop.hom r) = toStk z (valF (𝟙 (Sp F)) ⊤ r) := by`. Use `(gs_pull _ _ z ⊤ trivial _).trans (Eq.trans ?_ (toStk_valF' (𝟙 (Sp F)) ⊤ z trivial r).symm)` and prove the remaining obligations. Rewrite using `[← Over.comp_left, pt_fst]`.

Both sides reduce to the same expression. Establish `e₂` using `(VVRank.sv_pullS D.P.A 1 b (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) D.P.A).left) ν.th (snd (baseOver (Sp R)) D.P.A).left fun _ => Category.comp_id _) (pt ν x).left z hJ).trans (VVRank.sval_pullTo _ _ _ _ _ hJ)`. Establish `e₃ : ((pt ν x).left ≫ (b ▷ D.P.A).left) ≫ (snd (baseOver (Sp R)) D.P.A).left = (ν.eA x).left`. Rewrite using `[Category.assoc, VVRank.whisker_snd_left, ← Over.comp_left, lift_snd]`. Establish `e₄ : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J` using `(congrArg (toStk z) (ν.th_eq x)).trans (toStk_sF hJ _ _)`.

Rewrite `e₂` using `[e₃, ← e₄, map_mul, rg_eq]`. Establish `e₅` using `(H 0 x).trans ((hσ _ _ z _ hJ).symm.trans (e.trans (congrArg₂ (· * ·) e₁ e₂)))`. Rewrite `e₅` using `[pow_one, ← _root_.mul_assoc, ← map_mul]`. Conclude with `(toStk z).injective ((Units.mul_left_inj (rgU ν z)).1 e₅)`.
-/
theorem exists_smul_zero (hS : SecBaseChangeAnySt) {s : Fam D F 1} {f : N.X → N.A → F} (h : ν.FamV s f) :
    ∃ c : F, ∀ x, f 0 x = c * N.th x := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  have H := (famV_iff ν z s f).1 h
  let b : TF (R := R) F ⟶ baseOver (Sp R) := Over.homMk (TF (R := R) F).hom (Category.comp_id _)
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Sp F))
  have : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  have hg := EmbPull.isGenSec_pullS D.P hS b (isGenSec_base D.P ν.th ν.th_gen)
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB (φ' := fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left)
    (ε' := fun _ => (1 : ℤ)) (fun U _ g => by
      have p := prod_fam D F (𝟙 _) (ν.eX 0) 1 g
      have c₀ : cP D (DegPre.BF D F) (ν.eX 0) = 1 := by
        have := cPoint_nsmul D (DegPre.BF D F) 0 (ν.eX 0)
        rwa [zero_nsmul, pow_zero, ← map_zero ν.eX] at this
      simp only [Over.id_left, Category.id_comp] at p
      rw [p, c₀, _root_.one_mul, Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, inv_mul_cancel_right,
        Fintype.prod_unique, zpow_one]) (s.s (ν.eX 0))
  obtain ⟨r, hr⟩ := hg σ
  refine ⟨valF (𝟙 (Sp F)) ⊤ r, fun x => ?_⟩
  have e := sval_scale (φ := fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ε := fun _ => (1 : ℤ))
    (c := (fst (TF (R := R) F) D.P.A).left.appTop.hom r) hr (pt ν x).left hJ
  have e₁ : gs (pt ν x).left z ⊤ ((fst (TF (R := R) F) D.P.A).left.appTop.hom r) = toStk z (valF (𝟙 (Sp F)) ⊤ r) := by
    refine (gs_pull _ _ z ⊤ trivial _).trans (Eq.trans ?_ (toStk_valF' (𝟙 (Sp F)) ⊤ z trivial r).symm)
    rw [← Over.comp_left, pt_fst]
    rfl
  have e₂ := (VVRank.sv_pullS D.P.A 1 b (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) D.P.A).left)
      ν.th (snd (baseOver (Sp R)) D.P.A).left fun _ => Category.comp_id _) (pt ν x).left z hJ).trans
    (VVRank.sval_pullTo _ _ _ _ _ hJ)
  have e₃ : ((pt ν x).left ≫ (b ▷ D.P.A).left) ≫ (snd (baseOver (Sp R)) D.P.A).left = (ν.eA x).left := by
    rw [Category.assoc, VVRank.whisker_snd_left, ← Over.comp_left, lift_snd]
  have e₄ : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J :=
    (congrArg (toStk z) (ν.th_eq x)).trans (toStk_sF hJ _ _)
  rw [e₃, ← e₄, map_mul, rg_eq] at e₂
  have e₅ := (H 0 x).trans ((hσ _ _ z _ hJ).symm.trans (e.trans (congrArg₂ (· * ·) e₁ e₂)))
  rw [pow_one, ← _root_.mul_assoc, ← map_mul] at e₅
  exact (toStk z).injective ((Units.mul_left_inj (rgU ν z)).1 e₅)

end GlobalTheory.Ex.FamVal

/- English proof (translation)
Introduce `hL hL₂ R _ _ D _ hB F _ _ _ N ν k hk`. Establish `hG` using `hL.globalFns`. Use `⟨FamVal.exists_famV ν, fun s s' f => FamVal.famV_inj ν, fun s f => FamVal.famV_fe ν hG, ?_, fun s f h => ?_, fun p q w wv s s' f f' hp hw hwv h h' => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `FamFree.exists_fam_support (D := D) (F := F) hG hL₂.secTwist hB hk 0`. Take `⟨f, hf, -⟩` from `FamVal.exists_famV ν s`.

Use `⟨s, f, hf, fun h0 => (hs 0).2 ⟨0, by rw [smul_zero, add_zero]⟩ fun j => ?_⟩` and prove the remaining obligations. Establish `z₀ : ν.FamV (0 : Fam D F k) f`. Set `z : Sp F` to `IsLocalRing.closedPoint F`. Use `(FamVal.famV_iff ν z _ _).2 fun α x => ?_` and prove the remaining obligations. Rewrite using `[h0, Pi.zero_apply, Pi.zero_apply, map_zero, MulZeroClass.zero_mul]`.

Conclude with `(DVR.UUA.sval_zero_of (fun _ => rfl) _ z _ ((FamVal.good ν z).mem _ _)).symm`. Rewrite using `[FamVal.famV_inj ν hf z₀]`. Both sides reduce to the same expression. Take `⟨c, hc⟩` from `FamVal.exists_smul_zero ν hL₂.secBaseChangeAny h`. Use `⟨c, funext fun α => funext fun x => ?_⟩` and prove the remaining obligations.

Establish `e` using `FamVal.famV_fe ν hG h α 0 x`. Establish `u : N.uV 1 (N.c 0) (N.c α) x = 1`. Simplify using `[NumB.uV, cubN, N.cub.face]`. Rewrite `e` using `[zero_add, one_nsmul, u, hc, N.τ_zero_right, _root_.one_mul, _root_.mul_one, pow_one]`. Rewrite using `[e]`.

Conclude with `mul_left_comm _ _ _`. Rewrite using `[DVR.phiRel_iff hG p w hw]`. Use `⟨fun H => (FamVal.exists_famV ν s').unique h' (FamVal.phiVal_famV ν hp hwv h H), fun e => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `DVR.exists_phi hG p w hw hB s`. Substitute `e` using the available equality.

Take `rfl : s' = t` from `FamVal.famV_inj ν h' (FamVal.phiVal_famV ν hp hwv h ht)`. Conclude with `ht`.
-/
theorem GlobalTheory.Ex.brFam : Laws → Laws2 → BrFamSt := by
  intro hL hL₂ R _ _ D _ hB F _ _ _ N ν k hk
  have hG := hL.globalFns
  refine ⟨FamVal.exists_famV ν, fun s s' f => FamVal.famV_inj ν, fun s f => FamVal.famV_fe ν hG, ?_, fun s f h => ?_,
    fun p q w wv s s' f f' hp hw hwv h h' => ?_⟩
  · obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hL₂.secTwist hB hk 0
    obtain ⟨f, hf, -⟩ := FamVal.exists_famV ν s
    refine ⟨s, f, hf, fun h0 => (hs 0).2 ⟨0, by rw [smul_zero, add_zero]⟩ fun j => ?_⟩
    have z₀ : ν.FamV (0 : Fam D F k) f := by
      let z : Sp F := IsLocalRing.closedPoint F
      refine (FamVal.famV_iff ν z _ _).2 fun α x => ?_
      rw [h0, Pi.zero_apply, Pi.zero_apply, map_zero, MulZeroClass.zero_mul]
      exact (DVR.UUA.sval_zero_of (fun _ => rfl) _ z _ ((FamVal.good ν z).mem _ _)).symm
    rw [FamVal.famV_inj ν hf z₀]
    rfl
  · obtain ⟨c, hc⟩ := FamVal.exists_smul_zero ν hL₂.secBaseChangeAny h
    refine ⟨c, funext fun α => funext fun x => ?_⟩
    have e := FamVal.famV_fe ν hG h α 0 x
    have u : N.uV 1 (N.c 0) (N.c α) x = 1 := by
      simp [NumB.uV, cubN, N.cub.face]
    rw [zero_add, one_nsmul, u, hc, N.τ_zero_right, _root_.one_mul, _root_.mul_one, pow_one] at e
    rw [e]
    exact mul_left_comm _ _ _
  · rw [DVR.phiRel_iff hG p w hw]
    refine ⟨fun H => (FamVal.exists_famV ν s').unique h' (FamVal.phiVal_famV ν hp hwv h H), fun e => ?_⟩
    obtain ⟨t, ht⟩ := DVR.exists_phi hG p w hw hB s
    subst e
    obtain rfl : s' = t := FamVal.famV_inj ν h' (FamVal.phiVal_famV ν hp hwv h ht)
    exact ht

end
