import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulOfValLe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
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

namespace GlobalTheory.GSep.Labels

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp only [pow_zero, MonObj.comp_one]`. Consider the case `succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]`.
-/
theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]

open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in

/- English proof (translation)
Introduce `I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪`. Use `haveI : CharZero V := 𝔪.cn.2.2.2`. Establish `hL : GlobalTheory.UT.LL` using `GlobalTheory.firstFiveLaws`. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩`. Establish `hB` using `𝔪.D.tau_bimult`.

Establish `hk : 1 ≤ X₁.S.r * X₁.S.N`. Use `X₁.S.r_pos` as an intermediate fact. Use `X₁.S.N_ge` as an intermediate fact. Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))`. Take `⟨x, hx, xadd, -, xonto⟩` from `GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart`.

Take `⟨rig, e, -, he, -⟩` from `GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx`. Take `⟨f, f₁, f₂, f₃, f₄, -⟩` from `GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk`. Establish `tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y → y ^ (X₁.S.r * X₁.S.N) = 1` using `fun p y h => by`. Take `⟨w, hw⟩` from `𝔪.U.ext`. Conclude with `(h w hw).1`.

Establish `uniq : ∀ a (y : TFK (R` using `V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 → y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left → y = x a := by`. Introduce `a y hy hya`. Take `⟨b, rfl⟩` from `xonto y hy`. Take `⟨c, -, hc⟩` from `X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) : Over.mk (spMap ((algebraMap (Fracti …`. Establish `h1` using `hc a rfl`.

Establish `h2` using `hc b (by ext1`. Simplify using `only [Over.comp_left, Over.homMk_left]`. Rewrite using `[← hx b, hya])`. Rewrite using `[h1.trans h2.symm]`. Establish `ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a)` using `fun a => by`.

Take `⟨p, hp⟩` from `f₂ (x a) (he a).1`. Conclude with `⟨p, (f₁ _ _).2 hp.symm⟩`. Establish `yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N), p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a)`. Introduce `a mu`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, y, hpy, hq, hov⟩`. Take `rfl` from `uniq a y (tor p y hq) hov`. Conclude with `⟨p, hpy, hq⟩`. Introduce and unpack `⟨p, hpy, hq⟩`. Conclude with `⟨p, x a, hpy, hq, hx a⟩`.

Use `⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `ex a`. Conclude with `⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩`. Take `⟨p, hp⟩` from `exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)`. Take `⟨a, ha⟩` from `xonto (f p) (tor p _ ((f₁ _ _).2 rfl))`.

Conclude with `⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩`. Take `⟨p, hpy, hq⟩` from `(yyI a mu).1 h`. Rewrite using `[yyI]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p', hpy', hq'⟩`.

Establish `hpp : QkPt.Equiv _ _ p p'` using `(f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))`. Take `⟨z, hz, -⟩` from `(equiv_iff hB _ _).1 hpp`. Establish `e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z` using `𝔪.e₈.injective (by`. Rewrite using `[map_add, map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])`. Conclude with `⟨𝔪.e₈.symm z, e'⟩`.

Introduce `hc`. Take `⟨w, hw⟩` from `hc`. Use `⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩` and prove the remaining obligations. Use `show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'`. Rewrite using `[hpy, ← map_nsmul, ← map_add]`.

Rewrite using `[hw]`. Take `⟨p, hpy, hq⟩` from `(yyI a mu).1 h`. Take `⟨p', hpy', hq'⟩` from `(yyI a' mu').1 h'`. Use `(yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩` and prove the remaining obligations. Use `show p.y + p'.y = 𝔪.e₈ (mu + mu')`.

Rewrite using `[map_add, hpy, hpy']`. Rewrite using `[f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]`.
-/
theorem yy_hom : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ CongMod (X₁.S.r * X₁.S.N) mu' mu)) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (equiv_iff hB _ _).1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add, map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      exact ⟨𝔪.e₈.symm z, e'⟩
    · intro hc
      obtain ⟨w, hw⟩ := hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add]
      rw [hw]
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add, hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.GSep.Labels
