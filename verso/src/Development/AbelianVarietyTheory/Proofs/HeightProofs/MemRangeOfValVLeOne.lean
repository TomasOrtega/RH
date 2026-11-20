import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimesStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.RealisationValues.Proportional

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[vV]`. Rewrite using `[vV, ← WithZero.log_le_log (valV_ne_zero hx) one_ne_zero, WithZero.log_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valV_le_one_iff (x : K') : valV V x ≤ 1 ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    simp [vV]
  rw [vV, ← WithZero.log_le_log (valV_ne_zero hx) one_ne_zero, WithZero.log_one]
  omega

/- English proof (translation)
Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (IsDiscreteValuationRing.maximalIdeal V) x hx`. Establish `hu : IsUnit (d : V)`. Assume the negation of the conclusion as `hu`. Conclude with `d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)`. Take `⟨u, hu⟩` from `hu`.

Use `⟨n * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`.
-/
theorem mem_range_of_valV_le_one {x : K'} (hx : valV V x ≤ 1) : x ∈ Set.range (algebraMap V K') := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
    (IsDiscreteValuationRing.maximalIdeal V) x hx
  have hu : IsUnit (d : V) := by
    by_contra hu
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)
  obtain ⟨u, hu⟩ := hu
  refine ⟨n * ↑u⁻¹, ?_⟩
  rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

end Val

/- English proof (translation)
Establish `hint : ∀ a : 𝓞 K, (a : K) ∈ W` using `fun a => by`. Establish `h2 : IsIntegral W (a : K)` using `(RingOfIntegers.isIntegral_coe a).tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `g : 𝓞 K →+* W` to `(algebraMap (𝓞 K) K).codRestrict W hint`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g) (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)`. Use `⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha`. Establish `hu : IsUnit (g d)`.

Assume the negation of the conclusion as `hu`. Conclude with `d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))`. Take `⟨b, hb⟩` from `hu.exists_right_inv`. Establish `hb' : algebraMap (𝓞 K) K d * (b : K) = 1` using `congrArg Subtype.val hb`. Establish `: a = algebraMap (𝓞 K) K n * (b : K)` using `by rw [← hnd, mul_assoc, hb', mul_one]`.

Rewrite using `[this]`. Conclude with `W.mul_mem _ _ (hint n) b.2`.
-/
theorem exists_place_le {K : Type} [Field K] [NumberField K] (W : ValuationSubring K) :
    ∃ la : HeightOneSpectrum (𝓞 K), (la.valuation K).valuationSubring ≤ W := by
  have hint : ∀ a : 𝓞 K, (a : K) ∈ W := fun a => by
    have h2 : IsIntegral W (a : K) := (RingOfIntegers.isIntegral_coe a).tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2
    rw [← hy]
    exact y.2
  let g : 𝓞 K →+* W := (algebraMap (𝓞 K) K).codRestrict W hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)
  refine ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩,
    fun a ha => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hu : IsUnit (g d) := by
    by_contra hu
    exact d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (𝓞 K) K d * (b : K) = 1 := congrArg Subtype.val hb
  have : a = algebraMap (𝓞 K) K n * (b : K) := by rw [← hnd, mul_assoc, hb', mul_one]
  rw [this]
  exact W.mul_mem _ _ (hint n) b.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨g, hg2, hg1, hg⟩` from `(GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h`. Establish `hc` using `(GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'`. Conclude with `(GlobalTheory.Frames.frBor_iff_frChg z z' _).2 ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩`.
-/
theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero`.
-/
theorem wchar_ne_zero {J L : Type} [Fintype J] [Field L] (e : J → ℕ) (t : J → Lˣ) : wchar e t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero

/- English proof (translation)
Use `letI := io.toAlgebra`. Introduce and unpack `ψ ⟨z, t, hz, ht⟩ hint a n f hf`. Take `⟨w', hw'⟩` from `hL.bc _ _ ψ w`. Take `⟨-, hmul, hinv, -⟩` from `GlobalTheory.T.frameBorel_groupoid_properties E H Dw l Xo c T.Fr`. Establish `hb` using `hmul _ _ _ _ _ (hinv _ _ _ (frBor_map ψ h₀ hz hw')) ht`.

Use `⟨_, valV_wchar_eq_one (ex Dw a n) _ (hU T io ⟨w', hL.test _ _, hint w' hw'⟩ y _ hb), ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ ψ _ _ hw']`. Conclude with `hL.wt a n f hf _ _ w' y.1 (hL.test _ _) y.2.1 hb`.
-/
theorem evI_eq_unit_mul (hL : EvLaws Xo c) (hU : IntDiagUnit Xo c) {L : Type} [Field L] [Algebra c.F L]
    {y₀ w : FrPt Xo c L} {t₀ : Ix Dw → Lˣ} (h₀ : FrBor t₀ y₀ w) (T : CDVR) (io : c.F →+* T.Fr)
    (y : IntFr Xo c T io) : letI := io.toAlgebra
    ∀ (ψ : L →ₐ[c.F] T.Fr), (∃ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FrMap ψ y₀ z ∧ FrBor t z y.1) →
      (∀ w' : FrPt Xo c T.Fr, FrMap ψ w w' → Integral T io w') →
      ∀ a n, ∀ f ∈ sec Xo c a n, ∃ u : T.Fr, valV T.V u = 1 ∧ evI y f = u * ψ (evR Xo c f w) := by
  letI := io.toAlgebra
  rintro ψ ⟨z, t, hz, ht⟩ hint a n f hf
  obtain ⟨w', hw'⟩ := hL.bc _ _ ψ w
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.T.frameBorel_groupoid_properties E H Dw l Xo c T.Fr
  have hb := hmul _ _ _ _ _ (hinv _ _ _ (frBor_map ψ h₀ hz hw')) ht
  refine ⟨_, valV_wchar_eq_one (ex Dw a n) _ (hU T io ⟨w', hL.test _ _, hint w' hw'⟩ y _ hb), ?_⟩
  rw [← GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ ψ _ _ hw']
  exact hL.wt a n f hf _ _ w' y.1 (hL.test _ _) y.2.1 hb

/- English proof (translation)
Take `⟨la, hla⟩` from `exists_place_le (W.comap (algebraMap c.F L))`. Take `⟨Y, hY⟩` from `hM la`. Use `haveI : IsDiscreteValuationRing (la.valuation c.F).valuationSubring := inferInstance`. Take `⟨J, -, P, hP⟩` from `exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c hL.bc (la.valuation c.F).valuationSubring Y hY`. Take `⟨j, e, he, χ, w, t₀, hg, hw, h₀⟩` from `hP L W (fun a => hla a.2) y₀`.

Use `⟨w, t₀, h₀, fun T io => ?_⟩` and prove the remaining obligations. Use `letI := io.toAlgebra`. Introduce `ψ hψ w' hw'`. Use `(P j).int e he T io (ψ.comp χ) (fun a => ?_) (fun g hg' => hψ _ (hg g hg')) w' (frMap_trans _ _ _ χ ψ _ _ _ hw hw')` and prove the remaining obligations. Use `hψ _ (hla a.2)` as an intermediate fact.

Rewrite `this` using `[AlgHom.commutes]`. Then use the resulting hypothesis.
-/
theorem exists_integral_change (hL : EvLaws Xo c) (hM : ∀ la, ModelAt Xo c la) {L : Type} [Field L] [Algebra c.F L]
    (W : ValuationSubring L) (y₀ : FrPt Xo c L) :
    ∃ (w : FrPt Xo c L) (t₀ : Ix Dw → Lˣ), FrBor t₀ y₀ w ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      ∀ (ψ : L →ₐ[c.F] T.Fr), (∀ a ∈ W, ψ a ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ w' : FrPt Xo c T.Fr, FrMap ψ w w' → Integral T io w' := by
  obtain ⟨la, hla⟩ := exists_place_le (W.comap (algebraMap c.F L))
  obtain ⟨Y, hY⟩ := hM la
  haveI : IsDiscreteValuationRing (la.valuation c.F).valuationSubring := inferInstance
  obtain ⟨J, -, P, hP⟩ := exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c hL.bc
    (la.valuation c.F).valuationSubring Y hY
  obtain ⟨j, e, he, χ, w, t₀, hg, hw, h₀⟩ := hP L W (fun a => hla a.2) y₀
  refine ⟨w, t₀, h₀, fun T io => ?_⟩
  letI := io.toAlgebra
  intro ψ hψ w' hw'
  refine (P j).int e he T io (ψ.comp χ) (fun a => ?_) (fun g hg' => hψ _ (hg g hg')) w'
    (frMap_trans _ _ _ χ ψ _ _ _ hw hw')
  have := hψ _ (hla a.2)
  rwa [AlgHom.commutes] at this

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c h1 h2 h3 h Z T₁ T₂ ψ₁ ψ₂ y₁ y₂ m₁ m₂ hm₁ hm₂ hy₁ hy₂ _ hv a n f hf`. Take `⟨hL, hU, -⟩` from `GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c`. Take `⟨w, t₀, h₀, hint⟩` from `exists_integral_change hL (GlobalTheory.T.exists_global_model_goodLevel_all_primes E H Dw l Xo c h1 h2 h3).1 ((valV T₁.V).comap ψ₁).valuationSubring (genFr h Z)`. Take `⟨u₁, hu₁, e₁⟩` from `evI_eq_unit_mul hL hU h₀ T₁ _ y₁ _ hy₁ (hint T₁ _ _ fun x hx => mem_range_of_valV_le_one hx) a n f hf`. Take `⟨u₂, hu₂, e₂⟩` from `evI_eq_unit_mul hL hU h₀ T₂ _ y₂ _ hy₂ (hint T₂ _ _ fun x hx => mem_range_of_valV_le_one ((valV_le_one_iff _).2 (by`.

Establish `h4 : 0 ≤ vV T₁.V (ψ₁ x)` using `(valV_le_one_iff _).1 hx`. Establish `h5 : 0 ≤ (m₁ : ℤ) * vV T₂.V (ψ₂ x)` using `hv x ▸ mul_nonneg (Int.natCast_nonneg _) h4`. Conclude with `nonneg_of_mul_nonneg_right h5 (by exact_mod_cast hm₁) ))) a n f hf`. Use `replace e₁ : evI y₁ f = u₁ * ψ₁ (evR Xo c f w) := e₁`. Use `replace e₂ : evI y₂ f = u₂ * ψ₂ (evR Xo c f w) := e₂`.

Establish `e₀ : evR Xo c f w = wchar (ex Dw a n) t₀ * evC h Z f` using `hL.wt a n f hf _ t₀ _ w (hL.test _ _) (hL.test _ _) h₀`. Establish `hu0 : u₁ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hu₁`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e₁, e₀, mul_eq_zero, map_eq_zero, mul_eq_zero, or_iff_right hu0, or_iff_right (wchar_ne_zero _ _)]`. Use `hv (evR Xo c f w)` as an intermediate fact. Simplify `this` using `only [vV, e₁, e₂, map_mul, hu₁, hu₂, one_mul]`.
-/
theorem proportional_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) (T₁ T₂ : CDVR) (ψ₁ : Om Z →+* T₁.Fr) (ψ₂ : Om Z →+* T₂.Fr) (y₁ : IntFr Xo c T₁ (ψ₁.comp (algebraMap c.F (Om Z)))) (y₂ : IntFr Xo c T₂ (ψ₂.comp (algebraMap c.F (Om Z)))) (m₁ m₂ : ℕ), 0 < m₁ → 0 < m₂ → (letI := (ψ₁.comp (algebraMap c.F (Om Z))).toAlgebra; ∃ (z : FrPt Xo c T₁.Fr) (t : Ix Dw → (T₁.Fr)ˣ), FrMap ({ ψ₁ with commutes' := fun _ => rfl } : Om Z →ₐ[c.F] T₁.Fr) (genFr h Z) z ∧ FrBor t z y₁.1) → (letI := (ψ₂.comp (algebraMap c.F (Om Z))).toAlgebra; ∃ (z : FrPt Xo c T₂.Fr) (t : Ix Dw → (T₂.Fr)ˣ), FrMap ({ ψ₂ with commutes' := fun _ => rfl } : Om Z →ₐ[c.F] T₂.Fr) (genFr h Z) z ∧ FrBor t z y₂.1) → (∃ a : Om Z, vV T₁.V (ψ₁ a) ≠ 0) → (∀ a : Om Z, (m₂ : ℤ) * vV T₁.V (ψ₁ a) = (m₁ : ℤ) * vV T₂.V (ψ₂ a)) → ∀ a n, ∀ f ∈ sec Xo c a n, (evI y₁ f = 0 ↔ evC h Z f = 0) ∧ (m₂ : ℤ) * vV T₁.V (evI y₁ f) = (m₁ : ℤ) * vV T₂.V (evI y₂ f) := by
  intro E _ _ _ H Dw l Xo c h1 h2 h3 h Z T₁ T₂ ψ₁ ψ₂ y₁ y₂ m₁ m₂ hm₁ hm₂ hy₁ hy₂ _ hv a n f hf
  obtain ⟨hL, hU, -⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨w, t₀, h₀, hint⟩ := exists_integral_change hL (GlobalTheory.T.exists_global_model_goodLevel_all_primes E H Dw l Xo c h1 h2 h3).1
    ((valV T₁.V).comap ψ₁).valuationSubring (genFr h Z)
  obtain ⟨u₁, hu₁, e₁⟩ := evI_eq_unit_mul hL hU h₀ T₁ _ y₁ _ hy₁
    (hint T₁ _ _ fun x hx => mem_range_of_valV_le_one hx) a n f hf
  obtain ⟨u₂, hu₂, e₂⟩ := evI_eq_unit_mul hL hU h₀ T₂ _ y₂ _ hy₂
    (hint T₂ _ _ fun x hx => mem_range_of_valV_le_one ((valV_le_one_iff _).2 (by
      have h4 : 0 ≤ vV T₁.V (ψ₁ x) := (valV_le_one_iff _).1 hx
      have h5 : 0 ≤ (m₁ : ℤ) * vV T₂.V (ψ₂ x) := hv x ▸ mul_nonneg (Int.natCast_nonneg _) h4
      exact nonneg_of_mul_nonneg_right h5 (by exact_mod_cast hm₁) ))) a n f hf
  replace e₁ : evI y₁ f = u₁ * ψ₁ (evR Xo c f w) := e₁
  replace e₂ : evI y₂ f = u₂ * ψ₂ (evR Xo c f w) := e₂
  have e₀ : evR Xo c f w = wchar (ex Dw a n) t₀ * evC h Z f :=
    hL.wt a n f hf _ t₀ _ w (hL.test _ _) (hL.test _ _) h₀
  have hu0 : u₁ ≠ 0 := by
    rintro rfl
    simp at hu₁
  refine ⟨?_, ?_⟩
  · rw [e₁, e₀, mul_eq_zero, map_eq_zero, mul_eq_zero, or_iff_right hu0, or_iff_right (wchar_ne_zero _ _)]
  · have := hv (evR Xo c f w)
    simpa only [vV, e₁, e₂, map_mul, hu₁, hu₂, one_mul] using this

end GlobalTheory.RealisationValues.Proportional
