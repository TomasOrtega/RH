import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private half_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N
namespace UpperTheory.V.Z.Win.Birth
/- English proof (translation)
Introduce `hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw ⟨hreg, hwin⟩ hatt hpot`. Establish `h1` using `(_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩`. Establish `h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹)`. Use `(_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_` and prove the remaining obligations. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`.

Establish `hl : A.valuation (l : Ω) < 1`. Establish `h1` using `(hA ((l : ℕ) : 𝓞 T.L)).2 hlw`. Establish `e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω)` using `by simp`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Take `⟨e, k', hk', he, H⟩` from `twWts K n A hl`.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : Even (e - a) := by`. Use `he.sub ha` as an intermediate fact. Rewrite `this` using `[add_sub_add_right_eq_sub]`. Then use the resulting hypothesis. Conclude with `⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩`. Establish `h3` using `_root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2`.

Establish `h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r`. Use extensionality with `g : 2`. Rewrite using `[Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.inv_mul_cancel_right, K.rho_val]`. Both sides reduce to the same expression. Rewrite `h3` using `[h4]`.

Take `⟨P, hPair⟩` from `ptPair K n r hr`. Use `haveI : IsAlgClosure T.L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩`. Establish `h5 : Sd.IsAlgChar ι (K.twc n * κ⁻¹)`. Take `⟨χ, hc, art, a', b1, b2, b3⟩` from `h2`. Conclude with `⟨hc, art, χ, a', b1, b2, b3⟩`.

Establish `h6` using `awTw T.L Ω l 4 (by norm_num) ι _ _ h5 ⟨π, hreg, hatt⟩ (awOne T.L Ω l 4 (by norm_num) ι _ π hatt hwin)`. Rewrite `h6` using `[h4]`. Conclude with `⟨_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair, fun _ => h6.witA hpot⟩`.
-/
theorem ptAutR'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (ι : PadicAlgCl l ≃+* ℂ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∀ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ), Continuous κ → 0 < k → Even (a + n) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) → CuspidalRankFourRegularAlgebraicTotallyComplex π → Af.AttC ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) π → (∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → PotUnl (K.rhoQ n r) w) → IsAutCsdA ι (K.rhoQ n r) := by
  intro hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw ⟨hreg, hwin⟩ hatt hpot
  have h1 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩
  have h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    have hl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hlw
      have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
      rwa [e] at h1
    obtain ⟨e, k', hk', he, H⟩ := twWts K n A hl
    obtain ⟨m, hm⟩ : Even (e - a) := by
      have := he.sub ha
      rwa [add_sub_add_right_eq_sub] at this
    exact ⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2
  have h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.inv_mul_cancel_right, K.rho_val]
    rfl
  rw [h4] at h3
  obtain ⟨P, hPair⟩ := ptPair K n r hr
  haveI : IsAlgClosure T.L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have h5 : Sd.IsAlgChar ι (K.twc n * κ⁻¹) := by
    obtain ⟨χ, hc, art, a', b1, b2, b3⟩ := h2
    exact ⟨hc, art, χ, a', b1, b2, b3⟩
  have h6 := awTw T.L Ω l 4 (by norm_num) ι _ _ h5 ⟨π, hreg, hatt⟩ (awOne T.L Ω l 4 (by norm_num) ι _ π hatt hwin)
  rw [h4] at h6
  exact ⟨_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair, fun _ => h6.witA hpot⟩
end UpperTheory.V.Z.Win.Birth
end
