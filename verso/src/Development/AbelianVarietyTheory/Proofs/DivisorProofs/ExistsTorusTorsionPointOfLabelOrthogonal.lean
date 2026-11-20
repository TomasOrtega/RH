import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLabStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeight
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.TorPt

open GlobalTheory.ZH.TorusPerp in

/- English proof (translation)
Introduce `g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ χ hχ1 hlab q y hqy hqτ hq`. Use `haveI : CharZero V := 𝔪.cn.2.2.2`. Establish `: IsDomain X₁.o₁` using `X₁.ar.inj.isDomain _`. Establish `hL : GlobalTheory.UT.LL` using `GlobalTheory.firstFiveLaws`. Establish `hG` using `hL.1.globalFns`.

Establish `hA : AdmBase V (maximalIdeal V)` using `⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩`. Establish `hkpos : 0 < X₁.S.r * X₁.S.N` using `Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)`. Take `⟨x, hx, xadd, -, xonto⟩` from `GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart`. Take `⟨f, f₁, f₂, -, -, f₅⟩` from `GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos`. Establish `hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N)` using `X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)`.

Set `yb : X₁.S.R →+* AlgebraicClosure (FractionRing V)` to `(algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK`. Set `c₀ : (X₁.S.R)ˣ` to `Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit hkpos.ne').unit`. Set `ω : (AlgebraicClosure (FractionRing V))ˣ` to `Units.map yb.toMonoidHom c₀`. Establish `hωv : (ω : AlgebraicClosure (FractionRing V)) = yb (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)))` using `rfl`. Establish `hω : IsPrimitiveRoot ω (X₁.S.r * X₁.S.N)`.

Establish `: NeZero ((X₁.S.r * X₁.S.N : ℕ) : AlgebraicClosure (FractionRing V))` using `⟨Nat.cast_ne_zero.2 hkpos.ne'⟩`. Rewrite using `[← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic _ (yb.comp (algebraMap X₁.o₁ X₁.S.R))]`. Conclude with `(hζ.isRoot_cyclotomic hkpos).map`. Establish `hy : (TFK (R` using `V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK = spMap yb := (Spec.map_comp _ _).symm`. Set `h : Over.mk ((TFK (R` to `V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) := Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)`.

Establish `hh : h.left = spMap yb` using `hy`. Set `Φ` to `ptHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))`. Establish `hΦ : ∀ b, Φ (x b) = h ≫ X₁.ρ.pt b` using `fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))`. Establish `weil : ∀ b b', WeilIs 𝔪.A.A 𝔪.A.L (X₁.S.r * X₁.S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd X₁.S.g _ b b').val))` using `fun b b' => by`. Establish `w` using `GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h (X₁.ρ.weil b b' (c₀ ^ (eStd X₁.S.g _ b b').val) (by`.

Rewrite using `[pow_mul, map_pow]`. Use the proof step `rfl))`. Rewrite `w` using `[← hΦ, ← hΦ]`. Use `(GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ _ _ _ _ (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_` and prove the remaining obligations. Use `w using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← map_pow, ← map_unitOn, ← hh]`. Establish `pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n` using `fun n b => map_pow (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _) (Multiplicative.ofAdd b) n`. Establish `onto : ∀ b, ∃ q', f q' = x b` using `fun b => f₂ _ (by`. Rewrite using `[← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (X₁.S.r * X₁.S.N)), ZMod.natCast_self, zero_smul]`. Conclude with `(MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _).map_one)`.

Establish `hyf : y = f q` using `(f₁ q y).1 hq`. Establish `hq1 : y ^ (X₁.S.r * X₁.S.N) = 1`. Take `⟨w, hw⟩` from `𝔪.U.ext`. Conclude with `(hq w hw).1`. Take `⟨a', rfl⟩` from `xonto y hq1`.

Establish `haa : a' = τ`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_eStd _ _ _ fun b => ?_` and prove the remaining obligations. Take `⟨q', hq'⟩` from `onto b`. Establish `w₁` using `(f₅ q q' _).1 (weilQkIs_tor hG q q' hqy hqτ)`.

Rewrite `w₁` using `[← hyf, hq']`. Establish `e₁` using `unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB (weil a' b) w₁)`. Establish `hYY : 𝔪.YY b (𝔪.e₈.symm q'.y)` using `⟨q', x b, by simp, (f₁ _ _).2 hq'.symm, hx b⟩`. Establish `e₂` using `hlab b _ hYY`. Rewrite `e₂` using `[AddEquiv.apply_symm_apply]`.

Establish `e₃ : ω ^ (eStd X₁.S.g _ a' b).val = ω ^ (eStd X₁.S.g _ τ b).val`. Rewrite using `[e₁]`. Use `ext1`. Rewrite using `[e₂, Units.val_pow_eq_pow_val, hωv, pow_mul, map_pow, map_pow, map_pow]`. Both sides reduce to the same expression.

Establish `e₄` using `ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₃)`. Establish `e₅` using `eStd_add_left X₁.S.g _ (a' - τ) τ b`. Rewrite `e₅` using `[sub_add_cancel, e₄]`. Conclude with `left_eq_add.1 (e₅.trans (add_comm _ _))`. Substitute `haa` using the available equality.

Conclude with `hx a'`.
-/
theorem torus_label_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ b mu, 𝔪.YY b mu → (χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val))))) → ∀ (q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N)) (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), q.y = 0 → IsTor χ q.g → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q y → y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ χ hχ1 hlab q y hqy hqτ hq
  haveI : CharZero V := 𝔪.cn.2.2.2
  have : IsDomain X₁.o₁ := X₁.ar.inj.isDomain _
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos

  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let yb : X₁.S.R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit hkpos.ne').unit
  let ω : (AlgebraicClosure (FractionRing V))ˣ := Units.map yb.toMonoidHom c₀
  have hωv : (ω : AlgebraicClosure (FractionRing V)) = yb (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω : IsPrimitiveRoot ω (X₁.S.r * X₁.S.N) := by
    have : NeZero ((X₁.S.r * X₁.S.N : ℕ) : AlgebraicClosure (FractionRing V)) := ⟨Nat.cast_ne_zero.2 hkpos.ne'⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (yb.comp (algebraMap X₁.o₁ X₁.S.R))]
    exact (hζ.isRoot_cyclotomic hkpos).map

  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK = spMap yb := (Spec.map_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap yb := hy
  let Φ := ptHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
  have hΦ : ∀ b, Φ (x b) = h ≫ X₁.ρ.pt b := fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))
  have weil : ∀ b b', WeilIs 𝔪.A.A 𝔪.A.L (X₁.S.r * X₁.S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd X₁.S.g _ b b').val)) :=
    fun b b' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h (X₁.ρ.weil b b' (c₀ ^ (eStd X₁.S.g _ b b').val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← hΦ, ← hΦ] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ _ _ _ _
      (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  have pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n := fun n b =>
    map_pow (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _) (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q', f q' = x b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (X₁.S.r * X₁.S.N)), ZMod.natCast_self, zero_smul]
    exact (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _).map_one)
  have hyf : y = f q := (f₁ q y).1 hq
  have hq1 : y ^ (X₁.S.r * X₁.S.N) = 1 := by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (hq w hw).1
  obtain ⟨a', rfl⟩ := xonto y hq1
  have haa : a' = τ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hqy hqτ)
    rw [← hyf, hq'] at w₁
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB (weil a' b) w₁)
    have hYY : 𝔪.YY b (𝔪.e₈.symm q'.y) := ⟨q', x b, by simp, (f₁ _ _).2 hq'.symm, hx b⟩
    have e₂ := hlab b _ hYY
    rw [AddEquiv.apply_symm_apply] at e₂
    have e₃ : ω ^ (eStd X₁.S.g _ a' b).val = ω ^ (eStd X₁.S.g _ τ b).val := by
      rw [e₁]
      ext1
      rw [e₂, Units.val_pow_eq_pow_val, hωv, pow_mul, map_pow, map_pow, map_pow]
      rfl
    have e₄ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₃)
    have e₅ := eStd_add_left X₁.S.g _ (a' - τ) τ b
    rw [sub_add_cancel, e₄] at e₅
    exact left_eq_add.1 (e₅.trans (add_comm _ _))
  subst haa
  exact hx a'

/- English proof (translation)
Introduce `g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪`. Take `⟨h1, h2, h3, h4⟩` from `GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪`. Use `choose mu hmu using h1`. Establish `key : ∀ a nu, 𝔪.YY a nu ↔ (QuotientAddGroup.mk (𝔪.e₈ (mu a)) : 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range) = QuotientAddGroup.mk (𝔪.e₈ nu)`. Introduce `a nu`.

Rewrite using `[h3 a (mu a) nu (hmu a), QuotientAddGroup.eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hc choose w hw using hc`. Use `⟨𝔪.e₈ w, ?_⟩` and prove the remaining obligations. Establish `e : nu = mu a + (X₁.S.r * X₁.S.N) • w` using `funext fun v => by simpa using hw v`.

Rewrite using `[nsmulAddMonoidHom_apply, e, map_add, map_nsmul]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨z, hz⟩`. Rewrite `hz` using `[nsmulAddMonoidHom_apply]`. Introduce `v`.

Use `⟨𝔪.e₈.symm z v, ?_⟩` and prove the remaining obligations. Establish `e : nu = mu a + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z` using `𝔪.e₈.injective (by`. Rewrite using `[map_add, map_nsmul, AddEquiv.apply_symm_apply, hz]`. Use the proof step `abel)`. Rewrite using `[e]`.

Both sides reduce to the same expression. Set `yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range` to `AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (𝔪.e₈ (mu a))) fun a b => by`. Establish `h` using `(key (a + b) (mu a + mu b)).1 (h4 a b (mu a) (mu b) (hmu a) (hmu b))`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[map_add, QuotientAddGroup.mk_add]`.

Use `⟨yy, fun c => ?_, fun a nu => (key a nu)⟩` and prove the remaining obligations. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H α`. Take `⟨a, ha⟩` from `h2 (𝔪.e₈.symm α)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Use `(key a _).1 ha` as an intermediate fact. Rewrite `this` using `[AddEquiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem labels_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range, Function.Surjective yy ∧ ∀ a mu, 𝔪.YY a mu ↔ yy a = QuotientAddGroup.mk (𝔪.e₈ mu) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  choose mu hmu using h1
  have key : ∀ a nu, 𝔪.YY a nu ↔
      (QuotientAddGroup.mk (𝔪.e₈ (mu a)) : 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range) =
        QuotientAddGroup.mk (𝔪.e₈ nu) := by
    intro a nu
    rw [h3 a (mu a) nu (hmu a), QuotientAddGroup.eq]
    constructor
    · intro hc
      choose w hw using hc
      refine ⟨𝔪.e₈ w, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • w := funext fun v => by simpa using hw v
      rw [nsmulAddMonoidHom_apply, e, map_add, map_nsmul]
      abel
    · rintro ⟨z, hz⟩
      rw [nsmulAddMonoidHom_apply] at hz
      intro v
      refine ⟨𝔪.e₈.symm z v, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add, map_nsmul, AddEquiv.apply_symm_apply, hz]
        abel)
      rw [e]
      rfl
  let yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range :=
    AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (𝔪.e₈ (mu a))) fun a b => by
      have h := (key (a + b) (mu a + mu b)).1 (h4 a b (mu a) (mu b) (hmu a) (hmu b))
      refine h.trans ?_
      rw [map_add, QuotientAddGroup.mk_add]
  refine ⟨yy, fun c => ?_, fun a nu => (key a nu)⟩
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    obtain ⟨a, ha⟩ := h2 (𝔪.e₈.symm α)
    refine ⟨a, ?_⟩
    have := (key a _).1 ha
    rw [AddEquiv.apply_symm_apply] at this
    exact this

open GlobalTheory.ZH.TorusPerp GlobalTheory.ZH.PerpTorus GlobalTheory.TorusExt GlobalTheory.TorsionExt in
attribute [local instance] gtGroup in

/- English proof (translation)
Introduce `g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ hτ`. Use `haveI : CharZero V := 𝔪.cn.2.2.2`. Establish `hL : GlobalTheory.UT.LL` using `GlobalTheory.firstFiveLaws`. Establish `hB` using `𝔪.D.tau_bimult`. Establish `hkpos : 0 < X₁.S.r * X₁.S.N` using `Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)`.

Take `⟨yy, yyonto, hyy⟩` from `labels_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪`. Take `⟨x₀, hx₀⟩` from `X₁.div z₁`. Establish `hker : τ ∈ X₁.S.perp yy.ker` using `fun h hh => by`. Establish `h0 : 𝔪.YY h 0` using `(hyy h 0).2 (by rw [(AddMonoidHom.mem_ker).1 hh, map_zero]; rfl)`. Conclude with `hτ h ((GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V ev X m t δ 𝔪 h).2 h0)`.

Take `⟨mf, hmf⟩` from `exists_form X₁.S yy yyonto τ hker`. Establish `hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N)` using `X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)`. Set `ω : (FractionRing V)ˣ` to `Units.map (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R)).toMonoidHom (hζ.isUnit hkpos.ne').unit`. Establish `hωv : (ω : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)))` using `rfl`. Establish `hω1 : ω ^ (X₁.S.r * X₁.S.N) = 1` using `by ext1`.

Rewrite using `[Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one, Units.val_one]`. Set `χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ` to `(AddChar.zmodChar (X₁.S.r * X₁.S.N) hω1).toMonoidHom.comp mf.toMultiplicative`. Establish `hχ : ∀ α, χ (Multiplicative.ofAdd α) = ω ^ (mf α).val` using `fun _ => rfl`. Establish `hχ1 : χ ^ (X₁.S.r * X₁.S.N) = 1` using `MonoidHom.ext fun α => by show (ω ^ (mf α.toAdd).val) ^ (X₁.S.r * X₁.S.N) = 1`. Rewrite using `[pow_right_comm, hω1, one_pow]`.

Use `⟨χ, hχ1, fun g₀ hg₀ => ?_⟩` and prove the remaining obligations. Take `⟨q, hqy, hqg⟩` from `GlobalTheory.ZH.ClassWeight.exists_qkPt_tor hg₀ hχ1`. Establish `hsq : (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) ≫ X₁.ρ.P.A.hom = 𝟙 _ ≫ spMap 𝔪.yK`. Rewrite using `[Category.assoc, Over.w]`. Simplify using the standard rewrite rules.

Set `ℓ` to `𝔪.cart.1.lift (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) (𝟙 _) hsq`. Establish `hℓ : ℓ ≫ 𝔪.A.A.hom = (TFK (R` using `V) (FractionRing V)).hom := by`. Rewrite using `[𝔪.cart.1.lift_snd]`. Use `show _ = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V)))`. Rewrite using `[Algebra.algebraMap_self]`.

Conclude with `(Spec.map_id _).symm`. Set `xF : TFK (R` to `V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk ℓ hℓ`. Establish `hxF : xF.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left` using `𝔪.cart.1.lift_fst _ _ _`. Use `⟨q, xF, hqy, hqg, ?_, hxF⟩` and prove the remaining obligations. Establish `hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))` using `by ext; simp`.

Set `qb` to `qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf q`. Establish `hqb : QkExt (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) q qb` using `(qkExt_iff hB _ hf _ _).2 rfl`. Rewrite using `[qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow 𝔪.U hkpos hqb xF]`. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩`. Take `⟨f, f₁, -⟩` from `GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos`.

Establish `hqbf` using `(f₁ qb (f qb)).2 rfl`. Set `χb : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ` to `(Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ`. Establish `hχb1 : χb ^ (X₁.S.r * X₁.S.N) = 1` using `MonoidHom.ext fun α => by`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Use `show Units.map _ (χ α) ^ _ = 1`.

Rewrite using `[← map_pow, ← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply, map_one]`. Establish `hqbt : IsTor χb qb.g`. Establish `e1 : q.g = torusPt _ _ (Additive.ofMul χ)` using `(isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 (hqg ▸ hg₀))`. Use `show IsTor χb (gtExt _ _ hf q.g)`. Rewrite using `[e1, GlobalTheory.QkNumberField.gtExt_torusPt, isTor_iff]`.

Conclude with `isTorusPtF_torusPt _`. Establish `hlab : ∀ b mu, 𝔪.YY b mu → (χb (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val))))`. Introduce `b mu h`. Use `show algebraMap _ _ ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : FractionRing V)) = _`. Rewrite using `[hχ, hmf b _ ((hyy b mu).1 h), Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]`.

Establish `hover` using `torus_label_over g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ χb hχb1 hlab qb (f qb) hqy hqbt hqbf`. Establish `heq : fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ xF = f qb`. Use `Over.OverMorphism.ext (𝔪.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Rewrite using `[hover, Over.comp_left, Category.assoc, hxF, ← Category.assoc]`. Use `congr 1`.

Conclude with `(Spec.map_comp _ _).symm`. Rewrite using `[heq]`. Conclude with `hqbf`.
-/
theorem exists_torus_char : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ hτ
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hB := 𝔪.D.tau_bimult
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨yy, yyonto, hyy⟩ := labels_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have hker : τ ∈ X₁.S.perp yy.ker := fun h hh => by
    have h0 : 𝔪.YY h 0 := (hyy h 0).2 (by rw [(AddMonoidHom.mem_ker).1 hh, map_zero]; rfl)
    exact hτ h ((GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V ev X m t δ 𝔪 h).2 h0)
  obtain ⟨mf, hmf⟩ := exists_form X₁.S yy yyonto τ hker
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) := X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let ω : (FractionRing V)ˣ := Units.map (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R)).toMonoidHom (hζ.isUnit hkpos.ne').unit
  have hωv : (ω : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω1 : ω ^ (X₁.S.r * X₁.S.N) = 1 := by
    ext1
    rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one, Units.val_one]
  let χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ :=
    (AddChar.zmodChar (X₁.S.r * X₁.S.N) hω1).toMonoidHom.comp mf.toMultiplicative
  have hχ : ∀ α, χ (Multiplicative.ofAdd α) = ω ^ (mf α).val := fun _ => rfl
  have hχ1 : χ ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (mf α.toAdd).val) ^ (X₁.S.r * X₁.S.N) = 1
    rw [pow_right_comm, hω1, one_pow]
  refine ⟨χ, hχ1, fun g₀ hg₀ => ?_⟩

  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.ZH.ClassWeight.exists_qkPt_tor hg₀ hχ1
  have hsq : (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) ≫ X₁.ρ.P.A.hom = 𝟙 _ ≫ spMap 𝔪.yK := by
    rw [Category.assoc, Over.w]; simp
  let ℓ := 𝔪.cart.1.lift (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) (𝟙 _) hsq
  have hℓ : ℓ ≫ 𝔪.A.A.hom = (TFK (R := V) (FractionRing V)).hom := by
    rw [𝔪.cart.1.lift_snd]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V)))
    rw [Algebra.algebraMap_self]
    exact (Spec.map_id _).symm
  let xF : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk ℓ hℓ
  have hxF : xF.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left := 𝔪.cart.1.lift_fst _ _ _
  refine ⟨q, xF, hqy, hqg, ?_, hxF⟩
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    ext; simp
  let qb := qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf q
  have hqb : QkExt (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) q qb := (qkExt_iff hB _ hf _ _).2 rfl
  rw [qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow 𝔪.U hkpos hqb xF]
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos
  have hqbf := (f₁ qb (f qb)).2 rfl
  let χb : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ
  have hχb1 : χb ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show Units.map _ (χ α) ^ _ = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply, map_one]
  have hqbt : IsTor χb qb.g := by
    have e1 : q.g = torusPt _ _ (Additive.ofMul χ) := (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 (hqg ▸ hg₀))
    show IsTor χb (gtExt _ _ hf q.g)
    rw [e1, GlobalTheory.QkNumberField.gtExt_torusPt, isTor_iff]
    exact isTorusPtF_torusPt _
  have hlab : ∀ b mu, 𝔪.YY b mu → (χb (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))
        (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val)))) := by
    intro b mu h
    show algebraMap _ _ ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : FractionRing V)) = _
    rw [hχ, hmf b _ ((hyy b mu).1 h), Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]
  have hover := torus_label_over g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ χb hχb1 hlab qb (f qb) hqy hqbt hqbf
  have heq : fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ xF = f qb := by
    refine Over.OverMorphism.ext (𝔪.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hover, Over.comp_left, Category.assoc, hxF, ← Category.assoc]
    congr 1
    exact (Spec.map_comp _ _).symm
  rw [heq]
  exact hqbf

end GlobalTheory.Poinc.Sep.TorPt
