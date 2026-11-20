import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumUniqueness

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDetermined

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Take `⟨c, hc, h⟩` from `GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p) (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf)) (fun w f hf => by`. Take `⟨g, h⟩` from `p`. Establish `e` using `GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w`. Rewrite `e` using `[inv_inv, inv_inv]`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk, H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])`.

Use the proof step `(fun μ 𝓕 hμ h𝓕 f hf => by`. Rewrite using `[Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])`. Use `⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩` and prove the remaining obligations. Use `congrArg (om' p) (h f hf)` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply, om_om_inv, map_smul]`. Then use the resulting hypothesis.
-/
theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

/- English proof (translation)
Take `⟨w, hw⟩` from `Function.ne_iff.1 h0`. Use `⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩` and prove the remaining obligations. Unfold `heisO`. Rewrite using `[zero_add]`. Use `mul_ne_zero ?_ hw` and prove the remaining obligations.

Conclude with `(ψ.val_isUnit _).ne_zero`.
-/
theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

/- English proof (translation)
Assemble the required witnesses or components as `⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by linear_combination (e * e) * det_conj_mul V g + (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne …`.
-/
theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

/- English proof (translation)
Introduce `i j`. Rewrite using `[GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]`.
-/
theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_isDetAt he.1 S g`. Take `⟨y, hy⟩` from `exists_isDetAt he.1 T h`. Take `⟨r, hr, h1⟩` from `H.om_split e he g h hg hh x y hx hy`. Take `⟨r', hr', h2⟩` from `H'.om_split e he g h hg hh x y hx hy`. Take `⟨ℓ, hℓ, f, hf, hne⟩` from `GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he`.

Establish `e1` using `h1 ℓ hℓ f hf`. Rewrite `e1` using `[hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul]`. Establish `e2 : (c : ℂ) * r' = r`. Apply `mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)` to reduce the goal to its premises. Take the linear combination `e1`.

Establish `e3 : r' = r`. Use `congrArg norm e2` as an intermediate fact. Rewrite `this` using `[norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le]`. Then use the resulting hypothesis. Substitute `e3` using the available equality. Apply `Circle.ext` to reduce the goal to its premises.

Apply `mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')` to reduce the goal to its premises. Rewrite using `[e2, Circle.coe_one, one_mul]`.
-/
theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

/- English proof (translation)
Introduce `D ψ hψ S T χS χT om om' H H' p f hf`. Distinguish the cases in `h0 : f = 0`. Rewrite using `[h0, map_zero, map_zero]`. Take `⟨f₀, hf₀, h00⟩` from `exists_ne_zero_at_zero hψ hf h0`. Establish `hne : ∀ q, om' q f₀ ≠ 0` using `fun q hq => by`.

Use `om_inv_om om' q f₀` as an intermediate fact. Rewrite `this` using `[hq, map_zero]`. Conclude with `h00 (by rw [← this]; rfl)`. Use `choose c hc using exists_scalar H H'`. Establish `hmul : ∀ q q', c (q * q') = c q * c q'` using `fun q q' => by`.

Apply `Circle.ext` to reduce the goal to its premises. Apply `smul_left_injective ℂ (hne (q * q'))` to reduce the goal to its premises. Use `hc (q * q') f₀ hf₀` as an intermediate fact. Simplify using `only`. Rewrite using `[← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul, hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]`.

Establish `hcont : Continuous c`. Use `continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)` and prove the remaining obligations. Take `⟨w, hw⟩` from `Function.ne_iff.1 (hne q)`. Establish `h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q` using `(H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw`. Use `h1.congr ?_` and prove the remaining obligations.

Use `filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'`. Rewrite using `[hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']`. Both sides reduce to the same expression. Establish `hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1` using `fun γ hγ γ' hγ' => by`. Establish `h1` using `congrFun (hc (γ, γ') f₀ hf₀) 0`.

Rewrite `h1` using `[Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul]`. Apply `Circle.ext` to reduce the goal to its premises. Apply `mul_right_cancel₀ h00` to reduce the goal to its premises. Rewrite using `[← h1, Circle.coe_one, one_mul]`. Set `ν : GA D S × GA D T →* Circle` to `MonoidHom.mk' c hmul`.

Establish `hS` using `GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _)) (fun γ hγ => hrat γ hγ 1 (one_mem _)) (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))`. Establish `hT` using `GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _)) (fun γ hγ => hrat 1 (one_mem _) γ hγ) (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))`. Establish `h1 : c p = 1`. Establish `e : p = (p.1, 1) * (1, p.2)` using `by rw [Prod.mk_mul_mk, mul_one, one_mul]`. Rewrite using `[e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]`.

Rewrite using `[hc p f hf, h1, Circle.coe_one, one_smul]`.
-/
theorem agree_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

/- English proof (translation)
Use `GlobalTheory.WeilChange.hecke_mul (GlobalTheory.WeilChange.hecke_inv hχ) h` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis.
-/
theorem hecke_of_mul {χ ξ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (h : IsHeckeChar D (χ * ξ)) :
    IsHeckeChar D ξ := by
  have := GlobalTheory.WeilChange.hecke_mul (GlobalTheory.WeilChange.hecke_inv hχ) h
  rwa [inv_mul_cancel_left] at this

/- English proof (translation)
Take `⟨a, aval, -⟩` from `GlobalTheory.Member.exists_muVal D V ξ hξ h0`. Take `⟨x, hx⟩` from `aval.1 g`. Use `⟨x, hx, ⟨x, hx⟩, fun y hy => Circle.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← aval.2 g x hx, ← aval.2 g y hy]`.
-/
theorem exists_isTildeDet (V : HSp D) {ξ : (AE D)ˣ →* Circle} (hξ : IsHeckeChar D ξ)
    (h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D ξ) (g : GA D V) :
    ∃ x, IsDetRoot V g x ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.IsTildeDet V ξ g (ξ x) := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V ξ hξ h0
  obtain ⟨x, hx⟩ := aval.1 g
  refine ⟨x, hx, ⟨x, hx⟩, fun y hy => Circle.ext ?_⟩
  rw [← aval.2 g x hx, ← aval.2 g y hy]

/- English proof (translation)
Introduce `ψ S T χS χT ξ ξ' om om' h0 h0' H H' g h`. Establish `hξ` using `hecke_of_mul H.hecS H'.hecS`. Establish `hξ'` using `hecke_of_mul H.hecT H'.hecT`. Take `⟨om'', H'', hv⟩` from `GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H.std S T χS χT ξ ξ' om H hξ hξ' ⟨H.resS.1, fun η _ a => by rw [h0 a, pow_zero]⟩ ⟨H.resS.1, fun η _ a => by rw [h0' a, pow_zero]⟩`. Take `⟨x, hx, ha⟩` from `exists_isTildeDet S hξ' h0' g`.

Take `⟨y, hy, hb⟩` from `exists_isTildeDet T hξ h0 h`. Use `⟨ξ' x, ξ y, ha, hb, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[agree_on_theta D ψ H.std S T _ _ om' om'' H' H'' (g, h) f hf, hv g h x y hx hy, LinearMap.smul_apply]`.
-/
theorem weilDatumTwist (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumTwist D := by
  intro ψ S T χS χT ξ ξ' om om' h0 h0' H H' g h
  have hξ := hecke_of_mul H.hecS H'.hecS
  have hξ' := hecke_of_mul H.hecT H'.hecT
  obtain ⟨om'', H'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H.std S T χS χT ξ ξ' om H hξ hξ'
    ⟨H.resS.1, fun η _ a => by rw [h0 a, pow_zero]⟩ ⟨H.resS.1, fun η _ a => by rw [h0' a, pow_zero]⟩
  obtain ⟨x, hx, ha⟩ := exists_isTildeDet S hξ' h0' g
  obtain ⟨y, hy, hb⟩ := exists_isTildeDet T hξ h0 h
  refine ⟨ξ' x, ξ y, ha, hb, fun f hf => ?_⟩
  rw [agree_on_theta D ψ H.std S T _ _ om' om'' H' H'' (g, h) f hf, hv g h x y hx hy, LinearMap.smul_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(weilDatumTwist D).unique, weilDatumTwist D⟩`.
-/
theorem weilDatumDetermined (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumDetermined D :=
  ⟨(weilDatumTwist D).unique, weilDatumTwist D⟩

end GlobalTheory.WeilDetermined
