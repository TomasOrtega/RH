import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValAtSpecMap
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CubNMulOfPow
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDerGen
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TensOfBc
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyIdempotent
import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilreg
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHoldsStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}
  {C : Type} [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] {RC : Subalgebra O C}

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨halg, ⟨v, hv, hvp⟩, -, hR⟩` from `hT`. Establish `hp : p.Prime` using `Fact.out`. Establish `hR1 : 1 ≤ 𝔐.R p` using `le_trans (by norm_num) (𝔐.R_ge p hpS)`. Establish `hpow : p ^ 𝔐.R p = p * p ^ (𝔐.R p - 1)` using `by rw [← pow_succ', Nat.sub_add_cancel hR1]`. Use `haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩`.

Establish `hvI : v.Integers RC` using `⟨Subtype.val_injective, fun x => (hv x).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩`. Use `haveI : IsFractionRing RC C := hvI.isFractionRing`. Use `haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero`. Use `letI : Algebra (CR O y c') RC := (toRC _ RC hR).toAlgebra`. Establish `hφ : Function.Injective (algebraMap (CR O y c') RC)` using `fun a b h => Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))`.

Set `κ : FractionRing RC ≃+* C` to `(FractionRing.algEquiv RC C).toRingEquiv`. Establish `hκ : ∀ r : RC, κ (algebraMap RC _ r) = r` using `(FractionRing.algEquiv RC C).commutes`. Use `haveI : IsAlgClosed (FractionRing RC) := IsAlgClosed.of_ringEquiv C _ κ.symm`. Set `ik : Ω →+* FractionRing RC` to `κ.symm.toRingHom.comp (algebraMap Ω C)`. Establish `hik : ∀ r : CR O y c', ik r = algebraMap RC _ (algebraMap (CR O y c') RC r)` using `fun r => (RingEquiv.symm_apply_eq κ).2 (hκ (algebraMap (CR O y c') RC r)).symm`.

Establish `hfr : ik.comp (fracToField (CR O y c')) = PositivityTheory.UnitarySelfGeneration.fracMap hφ`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))` to reduce the goal to its premises. Rewrite using `[PositivityTheory.UnitarySelfGeneration.fracMap_comp]`. Use extensionality with `r`. Conclude with `(congrArg ik (IsFractionRing.lift_algebraMap _ r)).trans (hik r)`.

Set `Γ'` to `PositivityTheory.UnitarySelfGeneration.bcGroup P.Γ₁ hφ`. Set `F : Γ'.G.left ⟶ P.Γ₁.G.left` to `pullback.fst P.Γ₁.G.hom (spMap (algebraMap (CR O y c') RC))`. Establish `hF : F ≫ P.Γ₁.G.hom = Γ'.G.hom ≫ spMap (algebraMap (CR O y c') RC)` using `pullback.condition`. Establish `hbc : Γ'.IsBaseChange P.Γ₁ (algebraMap (CR O y c') RC) F`. Establish `h` using `isGrpPullback_pullback P.Γ₁.G (spMap (algebraMap (CR O y c') RC))`.

Use `⟨h.1, h.2, FractionRing (CR O y c'), inferInstance, algebraMap _ _, RingHom.id _, PositivityTheory.UnitarySelfGeneration.fracMap hφ, fun t => (P.Γ₁.pt t).left, Function.injective_id, rfl, PositivityTheory.UnitarySelfGeneration.fracMap_comp hφ, fun t => Over.w (P.Γ₁.pt t), fun t = …` and prove the remaining obligations. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`. Establish `hpt : ∀ t, (Γ'.pt t).left ≫ F ≫ P.i₁ = spMap ik ≫ (G.t₁.pt t).left` using `fun t => by`. Rewrite using `[P.pts₁, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfr]`. Conclude with `congrArg (· ≫ P.i₁) (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t)`.

Set `ζ' : RCˣ` to `Units.map (algebraMap (CR O y c') RC).toMonoidHom (P.ζ ^ p ^ (𝔐.R p - 1))`. Establish `hζ' : ((ζ' : RC) : C) = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1))`. Rewrite using `[← P.ζ_eq]`. Both sides reduce to the same expression. Establish `hζp : ζ' ^ p = 1` using `Units.ext (Subtype.ext (by`.

Rewrite using `[Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', ← map_pow, ← pow_mul, mul_comm, ← hpow, G.ζ_prim.pow_eq_one, map_one]`. Use the proof step `rfl))`. Take `⟨bi, hbi⟩` from `exists_bichar (D.p + D.q) p (p ^ 𝔐.R p) (dvd_pow_self p (by omega)) ζ' hζp G.e`. Set `Z : Over 𝔐.X` to `Over.mk ((Γ'.G ⊗ Γ'.G).hom ≫ spMap (algebraMap (CR O y c') RC) ≫ P.x)`. Establish `hw : ∀ u : Γ'.G ⊗ Γ'.G ⟶ Γ'.G, (u.left ≫ F ≫ P.i₁) ≫ 𝔐.t.G.hom = Z.hom` using `fun u => by`.

Rewrite using `[Category.assoc, Category.assoc, P.tors₁.isOver, ← Category.assoc F, hF, Category.assoc, ← Category.assoc u.left, Over.w u]`. Both sides reduce to the same expression. Set `X : (Γ'.G ⊗ Γ'.G ⟶ Γ'.G) → (Z ⟶ 𝔐.t.G)` to `fun u => Over.homMk (u.left ≫ F ≫ P.i₁) (hw u)`. Establish `hX : ∀ u, X u ^ p = 1` using `fun u => PositivityTheory.HtPt.Htat.tors_of_pt P.tors₁ (u.left ≫ F) (X u) (Category.assoc _ _ _).symm`. Establish `hs : ∀ a b, valAt (lift (Γ'.pt a) (Γ'.pt b)).left ⊤ le_top (PositivityTheory.HtPt.Weilfun.weilUnit 𝔐.t.cub p Z (X (fst _ _)) (X (snd _ _)) (hX _) (hX _)).val = algebraMap RC _ ((bi a b : RCˣ) : RC)`.

Introduce `a b`. Take `⟨x, rfl⟩` from `FunctionFamilyIdempotent.qmk_surj _ p a`. Take `⟨x', rfl⟩` from `FunctionFamilyIdempotent.qmk_surj _ p b`. Set `f₀` to `lift (Γ'.pt (qmk p x)) (Γ'.pt (qmk p x'))`. Establish `hf₀ : f₀.left ≫ Z.hom = spMap ik ≫ 𝔐.ξ`.

Rewrite using `[← hw (fst _ _), ← Category.assoc, ← Category.assoc, ← Over.comp_left, lift_fst, hpt, Category.assoc, Over.w]`. Both sides reduce to the same expression. Set `f : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Z` to `Over.homMk f₀.left hf₀`. Set `ψ : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Over.mk 𝔐.ξ` to `Over.homMk (spMap ik) rfl`. Establish `e1 : f ≫ X (fst _ _) = ψ ≫ G.t₂.pt (qmk _ (p ^ (𝔐.R p - 1) • x))`.

Rewrite using `[G.compat]`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f₀.left ≫ (fst Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _`. Rewrite using `[← Category.assoc, ← Over.comp_left, lift_fst, hpt]`. Establish `e2 : f ≫ X (snd _ _) = (ψ ≫ G.t₂.pt (qmk _ x')) ^ p ^ (𝔐.R p - 1)`.

Rewrite using `[← PositivityTheory.HtPt.Htat.comp_pow_pt, ← map_pow]`. Establish `: (qmk (p ^ 𝔐.R p) x') ^ p ^ (𝔐.R p - 1) = qmk _ (p ^ (𝔐.R p - 1) • x')` using `((qhom _ (p ^ 𝔐.R p)).map_pow (Multiplicative.ofAdd x') _).symm`. Rewrite using `[this, G.compat]`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f₀.left ≫ (snd Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _`.

Rewrite using `[← Category.assoc, ← Over.comp_left, lift_snd, hpt]`. Establish `t1 : ∀ u, (f ≫ X u) ^ p = 1` using `fun u => by`. Rewrite using `[← PositivityTheory.HtPt.Htat.comp_pow_pt, hX, MonObj.comp_one]`. Establish `t2 : ∀ z, (ψ ≫ G.t₂.pt z) ^ p ^ 𝔐.R p = 1` using `fun z => by`. Rewrite using `[← PositivityTheory.HtPt.Htat.comp_pow_pt, (G.t₂.onto _).2 ⟨z, rfl⟩, MonObj.comp_one]`.

Establish `k1` using `PositivityTheory.HtPt.Weilfun.weilUnit_comp 𝔐.t.cub p f (hX (fst _ _)) (hX (snd _ _)) (t1 _) (t1 _)`. Set `u : (FractionRing RC)ˣ` to `Units.map (algebraMap RC _).toMonoidHom (bi (qmk p x) (qmk p x'))`. Establish `hu : (u : FractionRing RC) = ik (G.ζ ^ (G.e (p ^ (𝔐.R p - 1) • x) x').val)`. Rewrite using `[map_nsmul, AddMonoidHom.nsmul_apply, pow_val_nsmul G.ζ_prim.pow_eq_one]`. Use `((RingEquiv.symm_apply_eq κ).2 ?_).symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = κ (algebraMap RC _ ((bi (qmk p x) (qmk p x') : RCˣ) : RC))`. Rewrite using `[hκ, hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', map_pow]`. Establish `k2` using `(G.weil (p ^ (𝔐.R p - 1) • x) x' _ ik (ψ ≫ G.t₂.pt (qmk _ _)) (ψ ≫ G.t₂.pt (qmk _ _)) u rfl rfl).2 hu`. Use `haveI : Subsingleton (Over.mk (spMap ik ≫ 𝔐.ξ)).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing RC)))`. Establish `k3` using `PositivityTheory.HtPt.Weilfun.weilUnit_eq_of_weilIs 𝔐.t.cub (p ^ 𝔐.R p) (t2 _) (t2 _) (unitOn u) (by rw [Nat.cast_pow]; exact k2)`.

Rewrite `k1` using `[weilUnit_level 𝔐.t.cub p (p ^ (𝔐.R p - 1)) _ hpow (t1 _) (t1 _) (t2 _) (t2 _) e1 e2, k3]`. Rewrite using `[PositivityTheory.HtPt.Weilreg.valAt_top]`. Use `(congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing RC))).hom.hom k1.symm).trans ?_` and prove the remaining obligations. Conclude with `PositivityTheory.HtPt.Weilreg.val_unitOn _`. Establish `hmem` using `bichar_mem hvI Γ' bi _ hs`.

Take `⟨ee, hee⟩` from `(GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth).2.2.2.2.1 RC Γ' F hbc`. Use `⟨_, tens_of_bc (N := TestPt.NAdd E (D.p + D.q) p) (C := C) (RC := RC) ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) ee hee (TestPt.testOrd P RC) rfl _ hmem, fun x x' => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((bi (qmk p x) (qmk p x') : RCˣ) : RC) : C) = _`. Rewrite using `[hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ']`.
-/
theorem kernel_mem [Fact p.Prime] (hpS : p ∈ S) [CharZero Ω] [IsLocallyNoetherian 𝔐.X]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (hT : IsTestPt p (CR O y c') RC) :
    ∃ Kf ∈ GR.tens (TestPt.testOrd P RC) (TestPt.testOrd P RC), ∀ x x' : Fin (D.p + D.q) → 𝓞 E,
      Kf (mkN p x, mkN p x') = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x x').val := by
  obtain ⟨halg, ⟨v, hv, hvp⟩, -, hR⟩ := hT
  have hp : p.Prime := Fact.out
  have hR1 : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hpow : p ^ 𝔐.R p = p * p ^ (𝔐.R p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hR1]
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hvI : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv x).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩
  haveI : IsFractionRing RC C := hvI.isFractionRing
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  letI : Algebra (CR O y c') RC := (toRC _ RC hR).toAlgebra
  have hφ : Function.Injective (algebraMap (CR O y c') RC) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  let κ : FractionRing RC ≃+* C := (FractionRing.algEquiv RC C).toRingEquiv
  have hκ : ∀ r : RC, κ (algebraMap RC _ r) = r := (FractionRing.algEquiv RC C).commutes
  haveI : IsAlgClosed (FractionRing RC) := IsAlgClosed.of_ringEquiv C _ κ.symm
  let ik : Ω →+* FractionRing RC := κ.symm.toRingHom.comp (algebraMap Ω C)
  have hik : ∀ r : CR O y c', ik r = algebraMap RC _ (algebraMap (CR O y c') RC r) := fun r =>
    (RingEquiv.symm_apply_eq κ).2 (hκ (algebraMap (CR O y c') RC r)).symm
  have hfr : ik.comp (fracToField (CR O y c')) = PositivityTheory.UnitarySelfGeneration.fracMap hφ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    rw [PositivityTheory.UnitarySelfGeneration.fracMap_comp]
    ext r
    exact (congrArg ik (IsFractionRing.lift_algebraMap _ r)).trans (hik r)
  let Γ' := PositivityTheory.UnitarySelfGeneration.bcGroup P.Γ₁ hφ
  let F : Γ'.G.left ⟶ P.Γ₁.G.left := pullback.fst P.Γ₁.G.hom (spMap (algebraMap (CR O y c') RC))
  have hF : F ≫ P.Γ₁.G.hom = Γ'.G.hom ≫ spMap (algebraMap (CR O y c') RC) := pullback.condition
  have hbc : Γ'.IsBaseChange P.Γ₁ (algebraMap (CR O y c') RC) F := by
    have h := isGrpPullback_pullback P.Γ₁.G (spMap (algebraMap (CR O y c') RC))
    refine ⟨h.1, h.2, FractionRing (CR O y c'), inferInstance, algebraMap _ _,
      RingHom.id _, PositivityTheory.UnitarySelfGeneration.fracMap hφ, fun t => (P.Γ₁.pt t).left, Function.injective_id, rfl,
      PositivityTheory.UnitarySelfGeneration.fracMap_comp hφ, fun t => Over.w (P.Γ₁.pt t), fun t => ?_,
      fun t => (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t).symm⟩
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hpt : ∀ t, (Γ'.pt t).left ≫ F ≫ P.i₁ = spMap ik ≫ (G.t₁.pt t).left := fun t => by
    rw [P.pts₁, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfr]
    exact congrArg (· ≫ P.i₁) (PositivityTheory.UnitarySelfGeneration.bcPt_fst P.Γ₁ hφ t)
  let ζ' : RCˣ := Units.map (algebraMap (CR O y c') RC).toMonoidHom (P.ζ ^ p ^ (𝔐.R p - 1))
  have hζ' : ((ζ' : RC) : C) = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) := by
    rw [← P.ζ_eq]; rfl
  have hζp : ζ' ^ p = 1 := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', ← map_pow, ← pow_mul, mul_comm, ← hpow,
      G.ζ_prim.pow_eq_one, map_one]; rfl))
  obtain ⟨bi, hbi⟩ := exists_bichar (D.p + D.q) p (p ^ 𝔐.R p) (dvd_pow_self p (by omega)) ζ' hζp G.e
  let Z : Over 𝔐.X := Over.mk ((Γ'.G ⊗ Γ'.G).hom ≫ spMap (algebraMap (CR O y c') RC) ≫ P.x)
  have hw : ∀ u : Γ'.G ⊗ Γ'.G ⟶ Γ'.G, (u.left ≫ F ≫ P.i₁) ≫ 𝔐.t.G.hom = Z.hom := fun u => by
    rw [Category.assoc, Category.assoc, P.tors₁.isOver, ← Category.assoc F, hF, Category.assoc,
      ← Category.assoc u.left, Over.w u]
    rfl
  let X : (Γ'.G ⊗ Γ'.G ⟶ Γ'.G) → (Z ⟶ 𝔐.t.G) := fun u => Over.homMk (u.left ≫ F ≫ P.i₁) (hw u)
  have hX : ∀ u, X u ^ p = 1 := fun u =>
    PositivityTheory.HtPt.Htat.tors_of_pt P.tors₁ (u.left ≫ F) (X u) (Category.assoc _ _ _).symm
  have hs : ∀ a b, valAt (lift (Γ'.pt a) (Γ'.pt b)).left ⊤ le_top
      (PositivityTheory.HtPt.Weilfun.weilUnit 𝔐.t.cub p Z (X (fst _ _)) (X (snd _ _)) (hX _) (hX _)).val =
      algebraMap RC _ ((bi a b : RCˣ) : RC) := by
    intro a b
    obtain ⟨x, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p a
    obtain ⟨x', rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p b
    let f₀ := lift (Γ'.pt (qmk p x)) (Γ'.pt (qmk p x'))
    have hf₀ : f₀.left ≫ Z.hom = spMap ik ≫ 𝔐.ξ := by
      rw [← hw (fst _ _), ← Category.assoc, ← Category.assoc, ← Over.comp_left, lift_fst, hpt, Category.assoc,
        Over.w]
      rfl
    let f : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Z := Over.homMk f₀.left hf₀
    let ψ : Over.mk (spMap ik ≫ 𝔐.ξ) ⟶ Over.mk 𝔐.ξ := Over.homMk (spMap ik) rfl
    have e1 : f ≫ X (fst _ _) = ψ ≫ G.t₂.pt (qmk _ (p ^ (𝔐.R p - 1) • x)) := by
      rw [G.compat]
      refine Over.OverMorphism.ext ?_
      change f₀.left ≫ (fst Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _
      rw [← Category.assoc, ← Over.comp_left, lift_fst, hpt]
    have e2 : f ≫ X (snd _ _) = (ψ ≫ G.t₂.pt (qmk _ x')) ^ p ^ (𝔐.R p - 1) := by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, ← map_pow]
      have : (qmk (p ^ 𝔐.R p) x') ^ p ^ (𝔐.R p - 1) = qmk _ (p ^ (𝔐.R p - 1) • x') :=
        ((qhom _ (p ^ 𝔐.R p)).map_pow (Multiplicative.ofAdd x') _).symm
      rw [this, G.compat]
      refine Over.OverMorphism.ext ?_
      change f₀.left ≫ (snd Γ'.G Γ'.G).left ≫ F ≫ P.i₁ = spMap ik ≫ _
      rw [← Category.assoc, ← Over.comp_left, lift_snd, hpt]
    have t1 : ∀ u, (f ≫ X u) ^ p = 1 := fun u => by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, hX, MonObj.comp_one]
    have t2 : ∀ z, (ψ ≫ G.t₂.pt z) ^ p ^ 𝔐.R p = 1 := fun z => by
      rw [← PositivityTheory.HtPt.Htat.comp_pow_pt, (G.t₂.onto _).2 ⟨z, rfl⟩, MonObj.comp_one]
    have k1 := PositivityTheory.HtPt.Weilfun.weilUnit_comp 𝔐.t.cub p f (hX (fst _ _)) (hX (snd _ _)) (t1 _) (t1 _)
    let u : (FractionRing RC)ˣ := Units.map (algebraMap RC _).toMonoidHom (bi (qmk p x) (qmk p x'))
    have hu : (u : FractionRing RC) = ik (G.ζ ^ (G.e (p ^ (𝔐.R p - 1) • x) x').val) := by
      rw [map_nsmul, AddMonoidHom.nsmul_apply, pow_val_nsmul G.ζ_prim.pow_eq_one]
      refine ((RingEquiv.symm_apply_eq κ).2 ?_).symm
      change _ = κ (algebraMap RC _ ((bi (qmk p x) (qmk p x') : RCˣ) : RC))
      rw [hκ, hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ', map_pow]
    have k2 := (G.weil (p ^ (𝔐.R p - 1) • x) x' _ ik (ψ ≫ G.t₂.pt (qmk _ _)) (ψ ≫ G.t₂.pt (qmk _ _)) u rfl rfl).2 hu
    haveI : Subsingleton (Over.mk (spMap ik ≫ 𝔐.ξ)).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing RC)))
    have k3 := PositivityTheory.HtPt.Weilfun.weilUnit_eq_of_weilIs 𝔐.t.cub (p ^ 𝔐.R p) (t2 _) (t2 _) (unitOn u)
      (by rw [Nat.cast_pow]; exact k2)
    rw [weilUnit_level 𝔐.t.cub p (p ^ (𝔐.R p - 1)) _ hpow (t1 _) (t1 _) (t2 _) (t2 _) e1 e2, k3] at k1
    rw [PositivityTheory.HtPt.Weilreg.valAt_top]
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing RC))).hom.hom k1.symm).trans ?_
    exact PositivityTheory.HtPt.Weilreg.val_unitOn _
  have hmem := bichar_mem hvI Γ' bi _ hs
  obtain ⟨ee, hee⟩ := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.2.1 RC Γ' F hbc
  refine ⟨_, tens_of_bc (N := TestPt.NAdd E (D.p + D.q) p) (C := C) (RC := RC)
    ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) ee hee (TestPt.testOrd P RC) rfl _ hmem,
    fun x x' => ?_⟩
  change (((bi (qmk p x) (qmk p x') : RCˣ) : RC) : C) = _
  rw [hbi, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hζ']

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hR1 : 1 ≤ 𝔐.R p` using `le_trans (by norm_num) (𝔐.R_ge p hpS)`. Use `haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Use `haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero`. Use `haveI : Finite (TestPt.NAdd E (D.p + D.q) p) := this`.

Use `haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')`. Establish `hφ : Function.Injective (toRC (CR O y c') RC hR)` using `fun a b h => Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))`. Establish `hBT` using `GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth`. Take `⟨θ, ⟨hθs, -⟩, hθk, hθc⟩` from `hBT.2.2.2.2.2 P.L P.M`. Establish `hom : P.Dh.om = LinearMap.range P.j` using `P.isHT.1`.

Establish `hj : ∀ w, P.j w ∈ P.Dh.om` using `fun w => by rw [hom]; exact ⟨w, rfl⟩`. Take `⟨Dv, hD1, hD2⟩` from `exists_der_gen (N := TestPt.NAdd E (D.p + D.q) p) (C := C) _ hφ Subtype.val_injective ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) hBT.1 p θ hθs (fun w => (hθk w).1) (P.j.codRestrict _ hj) io (TestPt.testOrd P RC) rfl`. Use `⟨Dv, hD1, fun u => ?_, fun x f hf => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩ : u.1 ∈ LinearMap.range P.j` from `by rw [← hom]; exact u.2`. Take `⟨a, ha⟩` from `(augIdeal (P.Γ₁.btOrder ⊤)).toCotangent_surjective (θ w)`.

Establish `ha1 : a.1.1 1 = 0` using `a.2`. Use `⟨⟨_, Submodule.subset_span ⟨a.1.1, a.1.2, rfl⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap Ω C ((a.1.1 1 : CR O y c') : Ω) = 0`. Rewrite using `[ha1]`. Simplify using the standard rewrite rules.

Use `(hD2 a.1 _ w (fun _ => rfl) ((cotMap_aug _ a).trans ha)).trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw)`. Take `⟨χ, w, hχ, hw, hHT⟩` from `P.isHT.2.2 x`. Take `⟨α, hα⟩` from `exists_alpha (E := E) (D.p + D.q) p (𝔐.R p) hR1`. Establish `h1` using `isHT_res P.Γ₁ P.Γ₂ (dvd_pow_self p (by omega)) P.tors₁ P.tors₂ P.M α (fun t => by`.

Take `⟨z, rfl⟩` from `FunctionFamilyIdempotent.qmk_surj _ p t`. Rewrite using `[← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, ← P.pts₂, hα, G.compat]) χ w hHT`. Establish `hval : ∀ z, ((((χ.comp α) (qmk p z) : (CR O y c')ˣ) : CR O y c') : Ω) = (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x z).val` using `fun z => by`. Rewrite using `[MonoidHom.comp_apply, hα]`. Establish `: χ (qmk _ (p ^ (𝔐.R p - 1) • z)) = P.ζ ^ (P.Dh.e x (p ^ (𝔐.R p - 1) • z)).val` using `hχ _`.

Rewrite using `[this, P.Dh_e, map_nsmul, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, P.ζ_eq, pow_val_nsmul G.ζ_prim.pow_eq_one]`. Establish `hm : (fun t => (((χ.comp α) t : (CR O y c')ˣ) : CR O y c')) ∈ P.Γ₁.btOrder ⊤`. Take `⟨s, hs, -⟩` from `h1`. Conclude with `char_mem _ _ s hs`. Use `(hD2 ⟨_, hm⟩ f w (fun z => ?_) ((cotMap_char _ _ hm).trans (hθc _ _ h1).symm)).trans (congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw.symm))` and prove the remaining obligations.

Take `⟨z', hz'⟩` from `FunctionFamilyIdempotent.qmk_surj _ p (Multiplicative.ofAdd z)`. Establish `: z = mkN p z'` using `(congrArg Multiplicative.toAdd hz').symm`. Substitute `this` using the available equality. Rewrite using `[hf]`. Conclude with `((congrArg (algebraMap Ω C) (hval z')).trans (map_pow _ _ _)).symm`.
-/
theorem exists_der [Fact p.Prime] (hpS : p ∈ S) [CharZero Ω]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) {g : ℕ}
    (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hR] (Fin g → RC)) :
    ∃ Dv : TestPt.testOrd P RC →ₗ[RC] ReciprocityTheory.PGsh.Up.LieDualModP p RC g, IsDerAt0 _ Dv ∧
      (∀ u : P.Dh.om, ∃ f : TestPt.testOrd P RC, f.1 0 = 0 ∧ Dv f = Submodule.Quotient.mk (io u)) ∧
      ∀ (x : Fin (D.p + D.q) → 𝓞 E) (f : TestPt.testOrd P RC),
        (∀ x', f.1 (mkN p x') = algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x x').val) →
        Dv f = Submodule.Quotient.mk (io ⟨P.Dh.h x, P.Dh.h_mem x⟩) := by
  have hp : p.Prime := Fact.out
  have hR1 : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  haveI : Finite (TestPt.NAdd E (D.p + D.q) p) := this
  haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')
  have hφ : Function.Injective (toRC (CR O y c') RC hR) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  have hBT := GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth
  obtain ⟨θ, ⟨hθs, -⟩, hθk, hθc⟩ := hBT.2.2.2.2.2 P.L P.M
  have hom : P.Dh.om = LinearMap.range P.j := P.isHT.1
  have hj : ∀ w, P.j w ∈ P.Dh.om := fun w => by rw [hom]; exact ⟨w, rfl⟩
  obtain ⟨Dv, hD1, hD2⟩ := exists_der_gen (N := TestPt.NAdd E (D.p + D.q) p) (C := C) _ hφ Subtype.val_injective
    ((algebraMap Ω C).comp (algebraMap (CR O y c') Ω)) (fun _ => rfl) hBT.1 p θ hθs (fun w => (hθk w).1)
    (P.j.codRestrict _ hj) io (TestPt.testOrd P RC) rfl
  refine ⟨Dv, hD1, fun u => ?_, fun x f hf => ?_⟩
  · obtain ⟨w, hw⟩ : u.1 ∈ LinearMap.range P.j := by rw [← hom]; exact u.2
    obtain ⟨a, ha⟩ := (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent_surjective (θ w)
    have ha1 : a.1.1 1 = 0 := a.2
    refine ⟨⟨_, Submodule.subset_span ⟨a.1.1, a.1.2, rfl⟩⟩, ?_, ?_⟩
    · change algebraMap Ω C ((a.1.1 1 : CR O y c') : Ω) = 0
      rw [ha1]; simp
    · refine (hD2 a.1 _ w (fun _ => rfl) ((cotMap_aug _ a).trans ha)).trans ?_
      exact congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw)
  · obtain ⟨χ, w, hχ, hw, hHT⟩ := P.isHT.2.2 x
    obtain ⟨α, hα⟩ := exists_alpha (E := E) (D.p + D.q) p (𝔐.R p) hR1
    have h1 := isHT_res P.Γ₁ P.Γ₂ (dvd_pow_self p (by omega)) P.tors₁ P.tors₂ P.M α (fun t => by
      obtain ⟨z, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, ← P.pts₂, hα, G.compat]) χ w hHT
    have hval : ∀ z, ((((χ.comp α) (qmk p z) : (CR O y c')ˣ) : CR O y c') : Ω) =
        (G.ζ ^ p ^ (𝔐.R p - 1)) ^ (G.e x z).val := fun z => by
      rw [MonoidHom.comp_apply, hα]
      have : χ (qmk _ (p ^ (𝔐.R p - 1) • z)) = P.ζ ^ (P.Dh.e x (p ^ (𝔐.R p - 1) • z)).val := hχ _
      rw [this, P.Dh_e, map_nsmul, Units.val_pow_eq_pow_val, Subalgebra.coe_pow, P.ζ_eq,
        pow_val_nsmul G.ζ_prim.pow_eq_one]
    have hm : (fun t => (((χ.comp α) t : (CR O y c')ˣ) : CR O y c')) ∈ P.Γ₁.btOrder ⊤ := by
      obtain ⟨s, hs, -⟩ := h1
      exact char_mem _ _ s hs
    refine (hD2 ⟨_, hm⟩ f w (fun z => ?_) ((cotMap_char _ _ hm).trans (hθc _ _ h1).symm)).trans
      (congrArg (fun z => Submodule.Quotient.mk (io z)) (Subtype.ext hw.symm))
    obtain ⟨z', hz'⟩ := FunctionFamilyIdempotent.qmk_surj _ p (Multiplicative.ofAdd z)
    have : z = mkN p z' := (congrArg Multiplicative.toAdd hz').symm
    subst this
    rw [hf]
    exact ((congrArg (algebraMap Ω C) (hval z')).trans (map_pow _ _ _)).symm

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Use `haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero`. Use `haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')`. Use `haveI := 𝔐.t.act.hom a`. Establish `h4` using `(GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁ 𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act a) (FunctionFamilyIdempotent.mulT _ p a) (by`.

Introduce `t`. Take `⟨x, rfl⟩` from `FunctionFamilyIdempotent.qmk_surj _ p t`. Rewrite using `[← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, FunctionFamilyIdempotent.mulT_qmk, G.t₁.lin, Over.comp_left, P.pts₁]`. Simplify using `only [Category.assoc])`. Establish `: TestPt.testOrd P RC ≤ (TestPt.testOrd P RC).comap (LinearMap.funLeft RC C fun (x : TestPt.NAdd E (D.p + D.q) p) i => Ideal.Quotient.mk _ a * x i)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `Submodule.subset_span ⟨_, h4 g hg, rfl⟩`. Conclude with `this hf`.
-/
theorem act_mem [Fact p.Prime]
    [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    (P : ChartPack G O c') (a : 𝓞 E) (f : TestPt.NAdd E (D.p + D.q) p → C) (hf : f ∈ TestPt.testOrd P RC) :
    (fun x : TestPt.NAdd E (D.p + D.q) p => f fun i => Ideal.Quotient.mk _ a * x i) ∈ TestPt.testOrd P RC := by
  have hp : p.Prime := Fact.out
  haveI := FunctionFamilyIdempotent.finite_tors (E := E) (D.p + D.q) hp.ne_zero
  haveI := FunctionFamilyIdempotent.frac_epi (CR O y c')
  haveI := 𝔐.t.act.hom a
  have h4 := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act a) (FunctionFamilyIdempotent.mulT _ p a) (by
      intro t
      obtain ⟨x, rfl⟩ := FunctionFamilyIdempotent.qmk_surj _ p t
      rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, FunctionFamilyIdempotent.mulT_qmk,
        G.t₁.lin, Over.comp_left, P.pts₁]
      simp only [Category.assoc])
  have : TestPt.testOrd P RC ≤ (TestPt.testOrd P RC).comap (LinearMap.funLeft RC C
      fun (x : TestPt.NAdd E (D.p + D.q) p) i => Ideal.Quotient.mk _ a * x i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, h4 g hg, rfl⟩
  exact this hf

end PositivityTheory.Xgn.TestGroupPoint
