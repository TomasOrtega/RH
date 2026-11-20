import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFrameOne
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsValuationClosure
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm.DvrScale

open GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale
open Classical

/- English proof (translation)
Take `⟨u', hu'⟩` from `h`. Use `⟨u' * u⁻¹, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap V (FractionRing V) r = algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V) * algebraMap V (FractionRing V) ((u : V) * r)`. Rewrite using `[← map_mul, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]`. Rewrite using `[e1, hu', Units.val_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasVal_of_unit_mul {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (u : Vˣ) {r : V} {n : ℤ}
    (h : HasVal ϖ (algebraMap V (FractionRing V) ((u : V) * r)) n) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨u', hu'⟩ := h
  refine ⟨u' * u⁻¹, ?_⟩
  have e1 : algebraMap V (FractionRing V) r =
      algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V) * algebraMap V (FractionRing V) ((u : V) * r) := by
    rw [← map_mul, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [e1, hu', Units.val_mul, map_mul]
  ring

attribute [local instance] gtGroup in

/- English proof (translation)
Introduce `g n F W Z i X₁ z₁ act V _ _ _ _ ev X _ m t δ 𝔪`. Use `haveI : CharZero V := 𝔪.cn.2.2.2`. Establish `hc : IsAdicComplete (maximalIdeal V) V` using `𝔪.cn.2.2.1`. Take `⟨hL, hL₂⟩` from `abelianSchemeLaws_all`. Take `⟨H, h₁, h₂, h₃, h₄⟩` from `hyps hL hL₂`.

Establish `hm` using `odd_level' X₁.ρ`. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩`. Establish `hB` using `𝔪.D.tau_bimult`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Use `choose Q hQ using QForm.exists_QVal hϖ 𝔪.D`.

Take `⟨v, hv, -⟩` from `GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ`. Establish `hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V)`. Use `X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨x, hx, xadd, xinj, xonto⟩` from `GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart`.

Take `⟨rig, e, hrig, he, hsec⟩` from `GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx`. Take `⟨t', ht⟩` from `hsec 1 X₁.ρ.th₁`. Take `⟨w₀, hw₀⟩` from `EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig`. Take `⟨th, ϑ, hE, hP, hgen⟩` from `exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀.1`. Establish `key` using `val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP _ hm hu`.

Take `⟨f, f₁, f₂, f₃, -⟩` from `GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) _ hm.pos`. Take `⟨r, hr⟩` from `hgen t'`. Take `⟨sc, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r`. Use `set Fc := AlgebraicClosure (FractionRing V) with hF`. Use `set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀`.

Establish `tv : ∀ a z J, Good 𝔪.A.L z J → cst (R` using `V) Fc z sc * @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) = cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z) (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ …`. Establish `b` using `X₁.ρ.th_val a`. Rewrite `b` using `[← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)]`. Conclude with `b) z J hJ)`. Establish `ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a)` using `fun a => by`.

Take `⟨q, hq⟩` from `f₂ (x a) (he a).1`. Conclude with `⟨q, (f₁ _ _).2 hq.symm⟩`. Establish `yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) → 𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y))` using `fun a q χ hq => ⟨qkShift hB q χ, x a, by`. Rewrite using `[AddEquiv.apply_symm_apply]`. Use `show q.y + (X₁.S.r * X₁.S.N) • χ = _`.

Rewrite using `[add_comm],`. Use the proof step `(f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩`. Establish `hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0` using `pow_ne_zero _ hm.pos.ne'`. Distinguish the cases in `h0 : sc = 0`. Establish `z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0` using `fun a => by`.

Take `⟨z⟩` from `CoefBasic.exists_pt (R := V) (F := Fc)`. Take `⟨J, hJ⟩` from `CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z`. Use `tv a z J hJ` as an intermediate fact. Rewrite `this` using `[h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul]`. Conclude with `CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)`.

Establish `z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0` using `fun a => (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)`. Use `⟨0, fun a => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `ex a`. Use `⟨_, 0, yyOf a q 0 hq, ?_⟩` and prove the remaining obligations. Rewrite using `[z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]`.

Establish `tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J = @id ((TFK (R` using `V) Fc).left.presheaf.stalk z) (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) * (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by`. Establish `b` using `congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)`. Simplify using `only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b`. Rewrite using `[CoefBasic.cst_eq]`. Conclude with `b`.

Establish `hvs : v sc ≠ ⊤` using `v.ne_top_iff.2 h0`. Establish `split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)` using `fun a => by`. Rewrite using `[← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]`. Establish `nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc` using `fun a h => by rw [split a, h, add_zero]`. Establish `h2 : 2 ≤ X₁.S.r * X₁.S.N` using `X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)`.

Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by`. Take `⟨p₀, hp₀⟩` from `exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0`. Take `⟨q', x', -, hx', -, hval⟩` from `(key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀`. Take `⟨a', rfl⟩` from `xonto x' (hx' w₀ hw₀.1).1`. Conclude with `⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩`.

Take `⟨s, hs⟩` from `WithTop.ne_top_iff_exists.1 hvs`. Use `⟨b, fun a => ?_⟩` and prove the remaining obligations. Take `⟨q, hq₁⟩` from `ex a`. Take `⟨_, ⟨χ, rfl⟩, hχ⟩` from `Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k) ⟨0, by`. Introduce and unpack `_ ⟨χ, rfl⟩`.

Distinguish the cases in `c : (X₁.S.r * X₁.S.N) • χ + q.y = 0`. Rewrite using `[c, QForm.Q_zero hϖ 𝔪.D hQ]`. Conclude with `zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩`. Establish `hk` using `((key q _ hq₁).1 _ _ (he a) (tv' a)).1 ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' => div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)`. Use `set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw`.

Establish `hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y` using `AddEquiv.apply_symm_apply _ _`. Establish `hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (mono W t δ w))) = (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)`. Take `⟨u, hpc⟩` from `𝔪.psi w`. Rewrite `hpc` using `[hew]`. Conclude with `hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))`.

Establish `hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0` using `fun h => hvs (by`. Rewrite using `[← hb]`. Use `show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤`. Rewrite using `[h, map_zero, AddValuation.map_zero])`. Establish `hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hb0) ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (𝔪.mono_ne_zero w))`.

Establish `hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w))) ≤ v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2)))`. Rewrite using `[map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]`. Express the relevant statement in the definitionally equal form `(X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤ (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)`. Rewrite using `[hb, split a, ← hs]`. Establish `hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hM2`.

Establish `e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) = (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ))`. Rewrite using `[← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe, nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]`. Rewrite using `[e]`. Conclude with `nsmul_le_nsmul_right (add_le_add le_rfl hk) _`. Take `⟨r', hr', -⟩` from `GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle`.

Use `⟨w, r', yyOf a q χ hq₁, ?_⟩` and prove the remaining obligations. Rewrite using `[hr', _root_.mul_assoc]`.
-/
theorem exists_dvd_pow : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, ∀ a, ∃ (w : Fin 8 → X) (r : V), 𝔪.YY a w ∧ 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hc : IsAdicComplete (maximalIdeal V) V := 𝔪.cn.2.2.1
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' X₁.ρ
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩
  have hB := 𝔪.D.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ 𝔪.D
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨t', ht⟩ := hsec 1 X₁.ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t'
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set Fc := AlgebraicClosure (FractionRing V) with hF
  set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀
  have tv : ∀ a z J, Good 𝔪.A.L z J → cst (R := V) Fc z sc *
      @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) =
      cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z)
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := X₁.ρ.th_val a
      rw [← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) := fun a => by
    obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, (f₁ _ _).2 hq.symm⟩
  have yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) →
      𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y)) := fun a q χ hq =>
    ⟨qkShift hB q χ, x a, by
      rw [AddEquiv.apply_symm_apply]
      show q.y + (X₁.S.r * X₁.S.N) • χ = _
      rw [add_comm],
      (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩
  have hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := Fc)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a =>
      (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)
    refine ⟨0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := ex a
    refine ⟨_, 0, yyOf a q 0 hq, ?_⟩
    rw [z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]

  have tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J =
      @id ((TFK (R := V) Fc).left.presheaf.stalk z)
        (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) *
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc :=
    fun a h => by rw [split a, h, add_zero]
  have h2 : 2 ≤ X₁.S.r * X₁.S.N := X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by
    obtain ⟨p₀, hp₀⟩ := exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0
    obtain ⟨q', x', -, hx', -, hval⟩ := (key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    exact ⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
  refine ⟨b, fun a => ?_⟩
  obtain ⟨q, hq₁⟩ := ex a
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k)
    ⟨0, by
      rintro _ ⟨χ, rfl⟩
      by_cases c : (X₁.S.r * X₁.S.N) • χ + q.y = 0
      · rw [c, QForm.Q_zero hϖ 𝔪.D hQ]
      · exact zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩
  have hk := ((key q _ hq₁).1 _ _ (he a) (tv' a)).1
    ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' =>
      div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)
  set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw
  have hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y := AddEquiv.apply_symm_apply _ _
  have hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (mono W t δ w))) =
      (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨u, hpc⟩ := 𝔪.psi w
    rw [hew] at hpc
    exact hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))
  have hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := fun h => hvs (by
    rw [← hb]; show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤; rw [h, map_zero, AddValuation.map_zero])
  have hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb0)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (𝔪.mono_ne_zero w))
  have hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w))) ≤
      v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))) := by
    rw [map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]
    change (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤
      (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)
    rw [hb, split a, ← hs]

    have hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM2
    have e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) =
        (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) +
          (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ)) := by
      rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
        nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]
    rw [e]
    exact nsmul_le_nsmul_right (add_le_add le_rfl hk) _
  obtain ⟨r', hr', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle
  refine ⟨w, r', yyOf a q χ hq₁, ?_⟩
  rw [hr', _root_.mul_assoc]

end GlobalTheory.Poinc.IntTerm.DvrScale
end
