import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValueStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShortBasisUniformizationLatticeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniformisedModelIntegralChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveChartsStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthPrimeToLevel

/- English proof (translation)
Establish `hN0 : N ≠ 0`. Introduce and unpack `rfl`. Conclude with `hN (by simp)`. Establish `h1` using `RPfVal.vLa_int_not_mem la hN`. Establish `h2 : (((N : ℕ) : 𝓞 K) : K) = (N : K)` using `map_natCast (algebraMap (𝓞 K) K) N`.

Rewrite `h1` using `[h2]`. Establish `h3` using `ho.2 (N : K)`. Rewrite `h3` using `[h1, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)]`. Establish `hx : algebraMap S.V S.Fr (N : S.V) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`.

Conclude with `hN0` after adjusting the coercions. Establish `hne` using `valV_ne_zero (V := S.V) hx`. Establish `h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1`. Unfold `vV at h3`. Rewrite using `[← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]`.

Unfold `valV at h4`. Rewrite `h4` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]`. Assume the negation of the conclusion as `hu`. Conclude with `h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)`.
-/
theorem isUnit_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h1 := RPfVal.vLa_int_not_mem la hN
  have h2 : (((N : ℕ) : 𝓞 K) : K) = (N : K) := map_natCast (algebraMap (𝓞 K) K) N
  rw [h2] at h1
  have h3 := ho.2 (N : K)
  rw [h1, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

/- English proof (translation)
Unfold `rr0`. Establish `h1 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)|` using `abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)`. Establish `h2 : (0 : ℝ) < Module.finrank ℚ D.host.E` using `by exact_mod_cast Module.finrank_pos`. Check the signs of the components of the expression.
-/
theorem rootDiscriminantDegreeRatio_pos (D : D7) : 0 < rr0 D := by
  unfold rr0
  have h1 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have h2 : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
  positivity

/- English proof (translation)
Establish `hφ : 0 ≤ φ`. Establish `h1 : 0 ≤ (e * (R * N ^ 3)) * φ` using `by nlinarith`. Conclude with `nonneg_of_mul_nonneg_right h1 (by positivity)`. Use `le_trans ?_ (mul_le_mul_of_nonneg_right hc hφ)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : 0 ≤ N ^ 4 * n` using `by positivity`. Establish `h2 : 0 ≤ N ^ 3` using `by positivity`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem err_le (R N n Dg Φ φ c e g₀ g₁ : ℝ) (hR : 0 < R) (hN : 0 < N) (hn : 0 ≤ n) (he : 0 < e) (hg₀ : 0 < g₀)
    (hg₁ : 1 ≤ g₁) (hΦ0 : 0 ≤ Φ) (hΦ : Φ ≤ e * (R * N ^ 3 * φ))
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g₀ ≤ c) : Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by nlinarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc hφ)
  calc Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ Dg ^ 2 * (e * (R * N ^ 3 * φ)) / (g₀ * 1) / e := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ := by field_simp
    _ ≤ _ := by
      have h1 : 0 ≤ N ^ 4 * n := by positivity
      have h2 : 0 ≤ N ^ 3 := by positivity
      gcongr
      linarith

/- English proof (translation)
Introduce `D T h j hj hinj EX w c _ hrun la hg y`. Use `letI := T.Q.H.starRing`. Take `⟨hlp, hn, h4, hc0, hc⟩` from `hrun`. Take `⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩` from `GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible S.V`.

Take `⟨⟨Q, hQ⟩, -⟩` from `GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ`. Take `⟨r, Φ, M0, ⟨hΦ0, b, hb1, hb2⟩, -, hM0, hjm, hΦ⟩` from `GlobalTheory.T.exists_short_basis_uniformization_lattice D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ`. Establish `hΦ' : Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la y)` using `hΦ`. Take `⟨⟨α, hα1, hα2⟩, -⟩` from `GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsCore.toLawsM EX`. Establish `hM : T.Q.l.M = D.host.g 0 * D.host.g 1` using `level_M T.toCore h.toLawsCore.toLawsM`.

Establish `hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j)`. Take `⟨st, hn⟩` from `h.nabPin j hj`. Use `GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1` as an intermediate fact. Substitute `this` using the available equality. Conclude with `hn`.

Establish `hMu : IsUnit ((T.Q.l.M : ℕ) : S.V)`. Use `isUnit_natCast la S _ e ho _ ?_` and prove the remaining obligations. Rewrite using `[hM, Nat.cast_mul]`. Introduce `hm`. Break down `la.isPrime.mem_or_mem hm with h1 | h1` into its components or cases.

Conclude with `hg 0 h1`. Conclude with `hg 1 h1`. Establish `hf1 : 1 ≤ D.R.f`. Establish `h1` using `GlobalTheory.DepthLink.finrank_host D`. Establish `h2 : 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`.

Use linear arithmetic over natural numbers and integers. Establish `hm2` using `D.R.two_le_m`. Establish `hr1 : 1 ≤ D.R.r`. Establish `h2` using `D.R.m_add_three_le_k`. Unfold `Ranks.r`.

Use linear arithmetic over natural numbers and integers. Establish `hn1 : 1 ≤ w.n` using `le_trans (Nat.mul_pos (by omega) hr1) hn`. Establish `hg0 : 2 ≤ D.host.g 0` using `(D.host.g_prime 0).two_le`. Establish `hg1 : 2 ≤ D.host.g 1` using `(D.host.g_prime 1).two_le`. Establish `hle : D.host.g 0 ≤ D.host.g 0 * D.host.g 1` using `Nat.le_mul_of_pos_right _ (by omega)`.

Establish `hg0' : (2 : ℝ) ≤ D.host.g 0` using `by exact_mod_cast hg0`. Establish `hg1' : (2 : ℝ) ≤ D.host.g 1` using `by exact_mod_cast hg1`. Establish `hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ)` using `by rw [hM]; exact_mod_cast hle`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast ho.1`. Establish `hDM : (WeightAlgebra.DF w : ℝ) * M0 < (T.Q.l.M : ℕ)`.

Break down `lt_or_ge j D.R.m with hjm' | hjm'` into its components or cases. Conclude with `((mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)).trans_lt (hc hjm' 0).1).trans_le hle'`. Rewrite using `[(hjm hjm').1, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnum : (WeightAlgebra.DF w : ℝ) ^ 2 * Φ / (T.Q.l.M : ℕ) / e ≤ c * (recPJ h j hj).phiC la y`.

Break down `lt_or_ge j D.R.m with hjm' | hjm'` into its components or cases. Rewrite using `[hM, Nat.cast_mul]`. Establish `hf' : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf1`. Establish `hm' : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm2`. Conclude with `err_le (rr0 D) _ w.n _ Φ _ c e _ _ (rootDiscriminantDegreeRatio_pos D) (by positivity) (Nat.cast_nonneg _) he' (by linarith) (by linarith) hΦ0 hΦ' (hc hjm' 0).2`.

Unfold `WeightAlgebra.PJ.phiC`. Rewrite using `[(hjm hjm').2, if_neg (not_lt.2 hjm')]`. Simplify using the standard rewrite rules. Establish `hA` using `GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ0 hb1 hb2 α hα1 hα2 hMu (wtA w) w.n (WeightAlgebra.DF w) e hn1 ho.1 (ReciprocityTheory.ChartRestri …`. Establish `hB` using `(GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn la).2.2.2.2 S io e ho z hz C`.

Establish `hsW` using `RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX w la hg`. Establish `hs0 : sWt (recB h.toLawsCore) hinj EX w ≠ 0`. Use `mul_ne_zero (fun h0 => RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX w la hg ?_) ?_` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `la.asIdeal.zero_mem`.

Establish `hq : D.host.q.Prime` using `D.host.hyp.1`. Establish `hd : D.host.d.Prime` using `D.host.hyp.2.1`. Conclude with `Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero)) (pow_ne_zero _ hd.ne_zero))`. Establish `hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ (⨅ f ∈ T.th j w, nval S.V e (evI z f)) + (((ramOverZ la : ℝ) * clOf w la : ℝ) : EReal)`. Rewrite using `[← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]`.

Use `le_iInf₂ fun f hf => ?_` and prove the remaining obligations. Rewrite using `[EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]`. Use `(GlobalTheory.T.thetaDepth_le_scaled_rule_value D T h j hj w hlp _ hs0 la y f hf).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `congrArg (fun x : ℝ => (x : EReal) + vAtV y f) hsW`. Establish `hnu : nusOf (recB h.toLawsCore) w (nuWt T w) la = (ramOverZ la : ℝ) * nuWt T w la + (ramOverZ la : ℝ) * clOf w la`.

Unfold `nusOf`. Rewrite using `[dif_neg (fun ⟨i, hi⟩ => hg i hi), ← mul_add, ← H1algLink.eWL_eq la]`. Both sides reduce to the same expression. Use `hdep.trans ?_` and prove the remaining obligations. Rewrite using `[hnu, add_right_comm, EReal.coe_add, EReal.coe_add]`.

Conclude with `add_le_add (hA.trans (add_le_add hB (EReal.coe_le_coe_iff.2 hnum))) le_rfl`.
-/
theorem depth_le : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro D T h j hj hinj EX w c _ hrun la hg y
  letI := T.Q.H.starRing
  obtain ⟨hlp, hn, h4, hc0, hc⟩ := hrun
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ0, b, hb1, hb2⟩, -, hM0, hjm, hΦ⟩ :=
    GlobalTheory.T.exists_short_basis_uniformization_lattice D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hΦ' : Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la y) := hΦ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsCore.toLawsM EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M T.toCore h.toLawsCore.toLawsM
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S.V) := by
    refine isUnit_natCast la S _ e ho _ ?_
    rw [hM, Nat.cast_mul]
    intro hm
    rcases la.isPrime.mem_or_mem hm with h1 | h1
    · exact hg 0 h1
    · exact hg 1 h1
  have hf1 : 1 ≤ D.R.f := by
    have h1 := GlobalTheory.DepthLink.finrank_host D
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hm2 := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ w.n := le_trans (Nat.mul_pos (by omega) hr1) hn
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ D.host.g 0 * D.host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by rw [hM]; exact_mod_cast hle
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < (T.Q.l.M : ℕ) := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · exact ((mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)).trans_lt (hc hjm' 0).1).trans_le hle'
    · rw [(hjm hjm').1, mul_zero]; linarith
  have hnum : (WeightAlgebra.DF w : ℝ) ^ 2 * Φ / (T.Q.l.M : ℕ) / e ≤ c * (recPJ h j hj).phiC la y := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · rw [hM, Nat.cast_mul]
      have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
      have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
      exact err_le (rr0 D) _ w.n _ Φ _ c e _ _ (rootDiscriminantDegreeRatio_pos D) (by positivity) (Nat.cast_nonneg _) he' (by linarith)
        (by linarith) hΦ0 hΦ' (hc hjm' 0).2
    · unfold WeightAlgebra.PJ.phiC
      rw [(hjm hjm').2, if_neg (not_lt.2 hjm')]
      simp
  have hA := GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ0 hb1 hb2 α hα1 hα2 hMu (wtA w) w.n (WeightAlgebra.DF w) e hn1 ho.1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.DF_wtA_le _ _) (by rw [hM]; exact (h4 0).trans hle) hDM
  have hB := (GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn la).2.2.2.2 S io e ho z hz C
  have hsW := RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX w la hg
  have hs0 : sWt (recB h.toLawsCore) hinj EX w ≠ 0 := by
    refine mul_ne_zero (fun h0 => RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX w la hg ?_) ?_
    · rw [h0]; exact la.asIdeal.zero_mem
    · have hq : D.host.q.Prime := D.host.hyp.1
      have hd : D.host.d.Prime := D.host.hyp.2.1
      exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
        (pow_ne_zero _ hd.ne_zero))
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) + (((ramOverZ la : ℝ) * clOf w la : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    refine (GlobalTheory.T.thetaDepth_le_scaled_rule_value D T h j hj w hlp _ hs0 la y f hf).trans (le_of_eq ?_)
    exact congrArg (fun x : ℝ => (x : EReal) + vAtV y f) hsW
  have hnu : nusOf (recB h.toLawsCore) w (nuWt T w) la =
      (ramOverZ la : ℝ) * nuWt T w la + (ramOverZ la : ℝ) * clOf w la := by
    unfold nusOf
    rw [dif_neg (fun ⟨i, hi⟩ => hg i hi), ← mul_add, ← H1algLink.eWL_eq la]
    rfl
  refine hdep.trans ?_
  rw [hnu, add_right_comm, EReal.coe_add, EReal.coe_add]
  exact add_le_add (hA.trans (add_le_add hB (EReal.coe_le_coe_iff.2 hnum))) le_rfl

end GlobalTheory.DepthPrimeToLevel
