import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSetStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupLoc

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Unfold `fdeg`. Establish `h2` using `IsTotallyComplex.finrank (K := E)`. Establish `hp : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem fdeg_pos' : 0 < fdeg E := by
  unfold fdeg
  have h2 := IsTotallyComplex.finrank (K := E)
  have hp : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

/- English proof (translation)
Unfold `Data.pnorm`. Check the signs of the components of the expression.
-/
theorem pnorm_nonneg' {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

/- English proof (translation)
Establish `hχ : ‖X.χ la γ‖ = 1`. Take `⟨n, hn, h⟩` from `X.χ_fin la`. Use `congrArg norm (h γ hγ)` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this`.

Unfold `Data.pnorm dmin`. Simplify using `only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]`. Rewrite using `[hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]`.
-/
theorem pnorm_lact' {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

/- English proof (translation)
Unfold `Data.pnorm`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hy]`.
-/
theorem pnorm_piecewise {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  classical
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

/- English proof (translation)
Distinguish the cases in `hy : y ∈ X.dom`. Rewrite using `[pnorm_piecewise X la P hy]`. Establish `: X.pnorm la (X.dom.piecewise P 0) y = 0`. Unfold `Data.pnorm`. Rewrite using `[Set.piecewise_eq_of_notMem _ _ _ hy]`.

Simplify using the standard rewrite rules. Rewrite using `[this, sq, zero_mul]`. Check the signs of the components of the expression.
-/
theorem pnorm_piecewise_le {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    X.pnorm la (X.dom.piecewise P 0) y ^ 2 ≤ X.pnorm la P y ^ 2 := by
  classical
  by_cases hy : y ∈ X.dom
  · rw [pnorm_piecewise X la P hy]
  · have : X.pnorm la (X.dom.piecewise P 0) y = 0 := by
      unfold Data.pnorm
      rw [Set.piecewise_eq_of_notMem _ _ _ hy]; simp
    rw [this, sq, zero_mul]; positivity

end GlobalTheory.SupLoc

open GlobalTheory.SupLoc in

/- English proof (translation)
Introduce `E _ _ _ r X la P M w x0 FF hr hP hM hw hw0 hΓL hTr hx0 hFF y hy`. Establish `hsec : X.IsSec la P` using `hP.1.1`. Take `⟨C, hC⟩` from `hP.1.2`. Distinguish the cases in `hy0 : X.pnorm la P y = 0`. Rewrite using `[hy0]`.

Simplify using the standard rewrite rules. Establish `hypos : 0 < X.pnorm la P y` using `lt_of_le_of_ne (pnorm_nonneg' _ _ _ _) (Ne.symm hy0)`. Use `set S := sSup (X.pnorm la P '' X.dom) with hSdef`. Establish `hbdd : BddAbove (X.pnorm la P '' X.dom)`. Use `⟨C, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hC x hx`. Establish `hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S` using `fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩`. Establish `hSpos : 0 < S` using `lt_of_lt_of_le hypos (hle y hy)`. Take `⟨_, ⟨z0, hz0, rfl⟩, hz0S⟩` from `exists_lt_of_lt_csSup ((show X.dom.Nonempty from ⟨y, hy⟩).image (X.pnorm la P)) (half_lt_self hSpos)`.

Establish `hhalf : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0` using `fun x hx => by`. Combine the linear relations using `[hle x hx]`. Establish `hz0pos : 0 < X.pnorm la P z0` using `by linarith`. Establish `hmax` using `maxBound_holds (E := E) r X la P M w hP hM hw hw0 hTr z0 hz0 hhalf hz0pos`. Take `⟨b, hb, hxo, hmaj⟩` from `ModeHalfC.orthonormalize X.toData hz0`.

Use `set x := rmul z0 b with hxdef`. Establish `hpx : X.pnorm la P x = X.pnorm la P z0` using `FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 z0 hz0 b hb`. Use `set ε := epStar M (fdeg E) w X.k0 with hεdef`. Establish `hf1 : (1 : ℝ) ≤ fdeg E` using `by exact_mod_cast (fdeg_pos' (E := E))`. Establish `hε : 0 < ε`.

Rewrite using `[hεdef]`. Unfold `epStar`. Establish `hk` using `X.minWeight_pos`. Establish `hl` using `Real.log_pos (show (1 : ℝ) < 2 by norm_num)`. Use `lt_min one_pos (div_pos Real.pi_pos ?_)` and prove the remaining obligations.

Establish `: 0 < (fdeg E : ℝ) * w + 2` using `by positivity`. Check the signs of the components of the expression. Establish `hshort : ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)`. Introduce `v hv hv0`. Take `⟨τ, hτ⟩` from `hmax v hv hv0`.

Rewrite `hτ` using `[← hmaj τ]`. Conclude with `hτ.trans (Finset.single_le_sum (f := fun τ => X.maj x τ (Data.emb τ.1 v)) (fun τ _ => ModeHalfC.maj_nonneg_orth X.toData hxo τ _) (Finset.mem_univ τ))`. Use `set ρ := chartRad E r w with hρdef`. Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100`.

Rewrite using `[hρdef]`. Unfold `chartRad`. Establish `h1 : 0 < (r : ℝ)` using `by linarith`. Establish `h2 : 0 < w + fdeg E` using `by linarith`. Rewrite using `[mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]`.

Use polynomial arithmetic with `[mul_le_mul hr1 (show (1:ℝ) ≤ w + fdeg E by linarith) zero_le_one h1.le]`. Establish `hmult` using `GlobalTheory.T.card_group_elements_chart_return_le E r X x ε ρ hr hxo hε hρ hΓL hshort`. Establish `hsub` using `GlobalTheory.T.subMeanValue_flagChart_invariantMeasure E r X.toData la w x P hr hxo hw hsec.1`. Use `set P' : Frame X.Ψ r → ℂ := X.dom.piecewise P 0 with hP'def`. Use `set Φ : Frame X.Ψ r → ℝ≥0∞ := fun u => ENNReal.ofReal (X.pnorm la P' u ^ 2) with hΦdef`.

Establish `hdomO` using `FourierCoefficientDomain.isOpen_dom X.toData`. Establish `hΦm : Measurable Φ`. Establish `hm` using `GlobalTheory.PeterssonCompare.measurable_pnorm X.toData la (P := P') (hsec.1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu) (fun u hu => by rw [hP'def, Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)`. Conclude with `ENNReal.measurable_ofReal.comp (hm.pow_const 2)`. Establish `hΦΓ : ∀ γ ∈ X.Γ, ∀ u ∈ X.dom, Φ (lact γ u) = Φ u`.

Introduce `γ hγ u hu`. Establish `hu'` using `GlobalTheory.MajInv.lact_mem_dom X.toData (X.Γ_stab γ hγ) hu`. Use `show ENNReal.ofReal (X.pnorm la P' (lact γ u) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)`. Rewrite using `[hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu', pnorm_lact' X.toData hsec hγ hu]`. Establish `hΦB : ∀ c ∈ Bor X.Ψ r, ∀ u ∈ X.dom, Φ (rmul u c) = Φ u`.

Introduce `c hc u hu`. Establish `hu'` using `OrthogonalFrameDomain.rmul_mem_dom X.toData hu hc`. Use `show ENNReal.ofReal (X.pnorm la P' (rmul u c) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)`. Rewrite using `[hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu', FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 u hu c hc]`. Use `set A := Metric.ball (0 : V (nd X.toData)) ρ ∩ OmF X.toData x with hAdef`.

Establish `hOm` using `ExF.isOpen_OmF X.toData x`. Establish `hA : MeasurableSet A` using `measurableSet_ball.inter hOm.measurableSet`. Establish `hAsub : A ⊆ OmF X.toData x` using `Set.inter_subset_right`. Establish `hmA : (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ c ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') c}.encard : ℝ≥0∞)) ≤ ENNReal.ofReal (multBd E r ε)`. Use `le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) hmult` and prove the remaining obligations.

Introduce and unpack `γ ⟨hγ, z, hz, z', hz', c, hc, he⟩`. Conclude with `⟨hγ, z, z', (mem_ball_zero_iff.1 hz.1).le, (mem_ball_zero_iff.1 hz'.1).le, c, hc, he⟩`. Establish `hunf` using `GlobalTheory.T.lintegral_invariant_chartSet_le_mul_fundamentalSet E r X.toData x0 x FF A _ Φ hx0 hxo hFF hA hAsub hΦm hΦΓ hΦB hmA`. Establish `hae : ∀ᵐ z ∂(muF X.toData x), z ∈ OmF X.toData x`. Establish `h1 : ∀ᵐ z ∂(volume.restrict (OmF X.toData x)), z ∈ OmF X.toData x` using `ae_restrict_mem hOm.measurableSet`.

Conclude with `(withDensity_absolutelyContinuous _ _).ae_le h1`. Establish `hball : ∫⁻ z in Metric.ball (0 : V (nd X.toData)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) ∂(muF X.toData x) = ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x)`. Establish `hset : A =ᵐ[muF X.toData x] Metric.ball (0 : V (nd X.toData)) ρ`. Establish `: OmF X.toData x =ᵐ[muF X.toData x] (Set.univ : Set (V (nd X.toData)))` using `ae_eq_univ.2 (ae_iff.1 hae)`. Establish `h2` using `(Filter.EventuallyEq.refl _ (Metric.ball (0 : V (nd X.toData)) ρ)).inter this`.

Rewrite `h2` using `[Set.inter_univ]`. Conclude with `h2`. Rewrite using `[Measure.restrict_congr_set hset]`. Use `setLIntegral_congr_fun_ae measurableSet_ball ?_` and prove the remaining obligations. Use `filter_upwards [hae] with z hz`.

Apply the tactic sequence `try intro _`. Use `show ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) = ENNReal.ofReal (X.pnorm la P' (cpt X.toData x z) ^ 2)`. Rewrite using `[hP'def, pnorm_piecewise X.toData la P hz]`. Establish `hFFle : ∫⁻ z in FF, Φ (cpt X.toData x0 z) ∂(muF X.toData x0) ≤ ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0)` using `lintegral_mono fun z => ENNReal.ofReal_le_ofReal (pnorm_piecewise_le X.toData la P _)`. Use `set C2 : ℝ := 2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r with hC2`.

Establish `hC2n : 0 ≤ C2` using `by positivity`. Establish `hyx : X.pnorm la P y ^ 2 ≤ 4 * X.pnorm la P x ^ 2`. Establish `h` using `hhalf y hy`. Rewrite `h` using `[← hpx]`. Use `pnorm_nonneg' X.toData la P y` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hconst : ENNReal.ofReal (locConst E r w ε) = ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ENNReal.ofReal (multBd E r ε))`. Rewrite using `[← ENNReal.ofReal_mul hC2n, ← ENNReal.ofReal_mul (by norm_num)]`. Use `congr 1`. Rewrite using `[hC2]`.

Unfold `locConst`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hball]`. Use `gcongr`.

Use `_ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * (ENNReal.ofReal (multBd E r ε) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0))) := by gcongr`. Conclude with `hunf.trans (by gcongr)`. Use `_ = _ := by rw [hconst]; ring`.
-/
theorem GlobalTheory.supLoc_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ) (x0 : Frame X.Ψ r) (FF : Set (V (nd X.toData))), 0 < r → P ∈ X.SS la → 0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) → IsOrth X.toData x0 → IsFundSet X.toData x0 FF → ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epStar M (fdeg E) w X.k0)) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) := by
  classical
  intro E _ _ _ r X la P M w x0 FF hr hP hM hw hw0 hΓL hTr hx0 hFF y hy
  have hsec : X.IsSec la P := hP.1.1
  obtain ⟨C, hC⟩ := hP.1.2
  by_cases hy0 : X.pnorm la P y = 0
  · rw [hy0]; simp
  have hypos : 0 < X.pnorm la P y := lt_of_le_of_ne (pnorm_nonneg' _ _ _ _) (Ne.symm hy0)

  set S := sSup (X.pnorm la P '' X.dom) with hSdef
  have hbdd : BddAbove (X.pnorm la P '' X.dom) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx
  have hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hSpos : 0 < S := lt_of_lt_of_le hypos (hle y hy)
  obtain ⟨_, ⟨z0, hz0, rfl⟩, hz0S⟩ := exists_lt_of_lt_csSup ((show X.dom.Nonempty from ⟨y, hy⟩).image (X.pnorm la P)) (half_lt_self hSpos)
  have hhalf : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0 := fun x hx => by
    linarith [hle x hx]
  have hz0pos : 0 < X.pnorm la P z0 := by linarith
  have hmax := maxBound_holds (E := E) r X la P M w hP hM hw hw0 hTr z0 hz0 hhalf hz0pos

  obtain ⟨b, hb, hxo, hmaj⟩ := ModeHalfC.orthonormalize X.toData hz0
  set x := rmul z0 b with hxdef
  have hpx : X.pnorm la P x = X.pnorm la P z0 := FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 z0 hz0 b hb
  set ε := epStar M (fdeg E) w X.k0 with hεdef
  have hf1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast (fdeg_pos' (E := E))
  have hε : 0 < ε := by
    rw [hεdef]; unfold epStar
    have hk := X.minWeight_pos
    have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    refine lt_min one_pos (div_pos Real.pi_pos ?_)
    have : 0 < (fdeg E : ℝ) * w + 2 := by positivity
    positivity
  have hshort : ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨τ, hτ⟩ := hmax v hv hv0
    rw [← hmaj τ] at hτ
    exact hτ.trans (Finset.single_le_sum (f := fun τ => X.maj x τ (Data.emb τ.1 v))
      (fun τ _ => ModeHalfC.maj_nonneg_orth X.toData hxo τ _) (Finset.mem_univ τ))
  set ρ := chartRad E r w with hρdef
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100 := by
    rw [hρdef]; unfold chartRad
    have h1 : 0 < (r : ℝ) := by linarith
    have h2 : 0 < w + fdeg E := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hr1 (show (1:ℝ) ≤ w + fdeg E by linarith) zero_le_one h1.le]
  have hmult := GlobalTheory.T.card_group_elements_chart_return_le E r X x ε ρ hr hxo hε hρ hΓL hshort
  have hsub := GlobalTheory.T.subMeanValue_flagChart_invariantMeasure E r X.toData la w x P hr hxo hw hsec.1

  set P' : Frame X.Ψ r → ℂ := X.dom.piecewise P 0 with hP'def
  set Φ : Frame X.Ψ r → ℝ≥0∞ := fun u => ENNReal.ofReal (X.pnorm la P' u ^ 2) with hΦdef
  have hdomO := FourierCoefficientDomain.isOpen_dom X.toData
  have hΦm : Measurable Φ := by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm X.toData la (P := P')
      (hsec.1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [hP'def, Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ γ ∈ X.Γ, ∀ u ∈ X.dom, Φ (lact γ u) = Φ u := by
    intro γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom X.toData (X.Γ_stab γ hγ) hu
    show ENNReal.ofReal (X.pnorm la P' (lact γ u) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu',
      pnorm_lact' X.toData hsec hγ hu]
  have hΦB : ∀ c ∈ Bor X.Ψ r, ∀ u ∈ X.dom, Φ (rmul u c) = Φ u := by
    intro c hc u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom X.toData hu hc
    show ENNReal.ofReal (X.pnorm la P' (rmul u c) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu',
      FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 u hu c hc]
  set A := Metric.ball (0 : V (nd X.toData)) ρ ∩ OmF X.toData x with hAdef
  have hOm := ExF.isOpen_OmF X.toData x
  have hA : MeasurableSet A := measurableSet_ball.inter hOm.measurableSet
  have hAsub : A ⊆ OmF X.toData x := Set.inter_subset_right
  have hmA : (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ c ∈ Bor X.Ψ r,
      lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') c}.encard : ℝ≥0∞)) ≤
      ENNReal.ofReal (multBd E r ε) := by
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) hmult
    rintro γ ⟨hγ, z, hz, z', hz', c, hc, he⟩
    exact ⟨hγ, z, z', (mem_ball_zero_iff.1 hz.1).le, (mem_ball_zero_iff.1 hz'.1).le, c, hc, he⟩
  have hunf := GlobalTheory.T.lintegral_invariant_chartSet_le_mul_fundamentalSet E r X.toData x0 x FF A _ Φ hx0 hxo hFF hA hAsub hΦm hΦΓ hΦB hmA

  have hae : ∀ᵐ z ∂(muF X.toData x), z ∈ OmF X.toData x := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF X.toData x)), z ∈ OmF X.toData x :=
      ae_restrict_mem hOm.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  have hball : ∫⁻ z in Metric.ball (0 : V (nd X.toData)) ρ,
      ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) ∂(muF X.toData x) =
      ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x) := by
    have hset : A =ᵐ[muF X.toData x] Metric.ball (0 : V (nd X.toData)) ρ := by
      have : OmF X.toData x =ᵐ[muF X.toData x] (Set.univ : Set (V (nd X.toData))) :=
        ae_eq_univ.2 (ae_iff.1 hae)
      have h2 := (Filter.EventuallyEq.refl _ (Metric.ball (0 : V (nd X.toData)) ρ)).inter this
      rw [Set.inter_univ] at h2
      exact h2
    rw [Measure.restrict_congr_set hset]
    refine setLIntegral_congr_fun_ae measurableSet_ball ?_
    filter_upwards [hae] with z hz
    try intro _
    show ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) = ENNReal.ofReal (X.pnorm la P' (cpt X.toData x z) ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hz]
  have hFFle : ∫⁻ z in FF, Φ (cpt X.toData x0 z) ∂(muF X.toData x0) ≤
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) :=
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal (pnorm_piecewise_le X.toData la P _)

  set C2 : ℝ := 2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r with hC2
  have hC2n : 0 ≤ C2 := by positivity
  have hyx : X.pnorm la P y ^ 2 ≤ 4 * X.pnorm la P x ^ 2 := by
    have h := hhalf y hy
    rw [← hpx] at h
    have := pnorm_nonneg' X.toData la P y
    nlinarith
  have hconst : ENNReal.ofReal (locConst E r w ε) =
      ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ENNReal.ofReal (multBd E r ε)) := by
    rw [← ENNReal.ofReal_mul hC2n, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hC2]; unfold locConst; ring
  calc ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (4 * X.pnorm la P x ^ 2) :=
        ENNReal.ofReal_le_ofReal hyx
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (X.pnorm la P x ^ 2) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x)) := by
        rw [← hball]; gcongr
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * (ENNReal.ofReal (multBd E r ε) *
          ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0))) := by
        gcongr
        exact hunf.trans (by gcongr)
    _ = _ := by rw [hconst]; ring
