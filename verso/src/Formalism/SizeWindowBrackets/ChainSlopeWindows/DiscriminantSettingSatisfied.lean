import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable
import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers

namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

/- English proof (authored)
Setting β and the initial scale to zero leaves every common window condition intact. For the two new upper bounds, the reciprocal of x² is nonnegative and remains nonnegative after multiplication by K ≥ 1. Thus both zero parameters meet their lower and upper bounds. Conversely, discard the bounds on these two parameters to recover the discriminant conditions.
-/
theorem discriminant_windows_iff : WindowsDIff := by
  intro P e K
  constructor
  · rintro ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩
    have h0 : (0 : ℝ) ≤ (P.x ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
    have hβ : (0 : ℝ) ≤ K * (P.x ^ 2)⁻¹ := mul_nonneg (by linarith) h0
    exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, le_refl (0 : ℝ), hβ, Co0, CoK, Y1, YX, le_refl (0 : ℝ), h0, bo0, bosb⟩
  · rintro ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, -, -, Co0, CoK, Y1, YX, -, -, bo0, bosb⟩
    exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
      ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩

/- English proof (authored)
The discriminant conditions are precisely the ordinary window conditions with the bounds on β and the initial scale omitted. The other inequalities are inherited directly.
-/
theorem discriminant_windows_of : WindowsDOf := by
  rintro P e K ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
    ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, -, -, Co0, CoK, Y1, YX, -, -, bo0, bosb⟩
  exact ⟨hε, hε1, he, hK, nx, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
    ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, Co0, CoK, Y1, YX, bo0, bosb⟩

/- English proof (authored)
The logarithm of a natural number in the stated real convention is nonnegative, including zero at the zero input. The denominator is also nonnegative, so their quotient is nonnegative.
-/
lemma logdiv_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) / (p : ℝ) :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/- English proof (authored)
For each served prime, every omitted top index must be marked bad, and any prime with such an omission belongs to the designated prime set. Thus for primes in that set the omission count is at most the bad count, and for other primes it is zero. Multiply by the nonnegative weights and extend the resulting sum to the full designated set. Factoring out 4am leaves the assumed weighted count, which is at most R.
-/
theorem out_discriminant_bound : OutD := by
  intro τ Ps PR cl TT TTp BAD m a R hm ha hT2 hBad
  have hco : ∀ p : ℕ, 0 ≤ 4 * m * a * (Real.log p / p) := fun p => by
    have := logdiv_nonneg p
    positivity
  have h1 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ PR then 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hb := hBad p hp.1 hp.2
    by_cases hps : p ∈ PR
    · rw [if_pos hps]
      refine mul_le_mul_of_nonneg_left ?_ (hco p)
      have hsub : TT \ TTp p ⊆ TT.filter fun t => BAD p t := by
        intro t ht
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.1 ht).1, (hb t ht).2⟩
      exact_mod_cast Finset.card_le_card hsub
    · rw [if_neg hps]
      have hemp : TT \ TTp p = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        exact hps (hb t ht).1
      rw [hemp]; simp
  have h2 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ PR then 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) ≤
      ∑ p ∈ PR, 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => mul_nonneg (hco p) (Nat.cast_nonneg _))
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have h3 : ∑ p ∈ PR, 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) =
      4 * a * m * badPrimeLogWeightedCount PR TT BAD := by
    unfold badPrimeLogWeightedCount
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h4 : 4 * a * m * badPrimeLogWeightedCount PR TT BAD ≤ 4 * a * m * R :=
    mul_le_mul_of_nonneg_left hT2 (by positivity)
  linarith

/- English proof (authored)
The second-prime estimate bounds the loss by summing 4amT log(p)/p over candidates whose indicator threshold is exceeded. Each such term is exactly the contribution from the indicator part of the weighted sum multiplied by 2amT. The remaining signature contributions are nonnegative, so the loss is bounded by 2amT times the full weighted sum. Use its bound by R.
-/
theorem second_discriminant_bound : SecondD := by
  intro Ps cand cl Sig θ m T a R hm hT ha hSig hW hcl
  have h1 := second_term_le Ps cand cl Sig θ m T a hm hT ha hcl
  have hc : 0 ≤ 2 * a * m * T := by positivity
  have h2 : ∑ p ∈ cand, (if θ < Sig p then 4 * (m * T * a) * Real.log p / p else 0) ≤
      2 * a * m * T * lhsW cand θ Sig := by
    unfold lhsW
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hl := logdiv_nonneg p
    have hs := hSig p hp
    have h0 : 0 ≤ 2 * a * m * T * (Real.log p / p * (4 * Sig p)) := by positivity
    split_ifs
    · have e : 2 * a * m * T * (Real.log p / p * (2 + 4 * Sig p)) =
          4 * (m * T * a) * Real.log p / p + 2 * a * m * T * (Real.log p / p * (4 * Sig p)) := by ring
      rw [e]; linarith
    · rw [zero_add]; exact h0
  have h3 := mul_le_mul_of_nonneg_left hW hc
  linarith

/- English proof (authored)
Multiply the pointwise bound on the index by the nonnegative logarithm of p. The resulting term is the signature part of the weighted candidate sum scaled by amT. The indicator contribution is nonnegative, so including it can only increase the upper bound. Summing and using the assumed candidate bound yields amTR.
-/
theorem io_discriminant_bound : IoD := by
  intro cand Sig io θ m T a R hm hT ha hW hio
  have hc : 0 ≤ a * m * T := by positivity
  have h2 : ∑ p ∈ cand, Real.log p * io p ≤ a * m * T * lhsW cand θ Sig := by
    unfold lhsW
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have h := mul_le_mul_of_nonneg_left (hio p hp) (Real.log_natCast_nonneg p)
    have hl := logdiv_nonneg p
    have hi : (0 : ℝ) ≤ (if θ < Sig p then (2 : ℝ) else 0) := by split_ifs <;> norm_num
    have h0 : 0 ≤ a * m * T * (Real.log p / p * (if θ < Sig p then (2 : ℝ) else 0)) := by positivity
    have e : a * m * T * (Real.log p / p * ((if θ < Sig p then (2 : ℝ) else 0) + 4 * Sig p)) =
        Real.log p * (2 * Sig p * (2 * (m * T * a) / p)) +
          a * m * T * (Real.log p / p * (if θ < Sig p then (2 : ℝ) else 0)) := by ring
    rw [e]; linarith
  have h3 := mul_le_mul_of_nonneg_left hW hc
  linarith

/- English proof (authored)
Write z = x to the power ε and r = 1/x. Since a = xb, the coefficient 4a times x to the power −2 + ε is 4bzr. The large-x estimate bounds 100zr by the slope allowance. Multiply by the nonnegative factor 4b/100 to get the desired bound by b times that allowance. Scaling by mT gives the claimed size estimate.
-/
lemma sizeOut_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tOutD P m T ≤ sg P K * unitU P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOutD unitU
  have h9 := F.xpos
  have hpow : P.x ^ (-2 + P.ε) = P.x⁻¹ ^ 2 * z := by
    rw [Real.rpow_add h9, Real.rpow_neg h9.le, ← F.hz, Real.rpow_ofNat, F.r2]
  have key : 4 * P.a * P.x ^ (-2 + P.ε) ≤ sg P K * P.b := by
    rw [F.ha, hpow]
    calc 4 * (P.x * P.b) * (P.x⁻¹ ^ 2 * z)
        = P.b * (4 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 1) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith

/- English proof (authored)
Write r = 1/x. The coefficient 2a/x⁹ is 2br⁸ because a = xb. Since 0 < r ≤ 1, r⁷ ≤ 1. The large-x estimate at exponent zero bounds 100r by the slope allowance. Thus 2br⁸, which is (2b/100)r⁷ times 100r, is at most b times the allowance.
-/
lemma size_ninth_power_bound {P : Par} {e K : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) :
    2 * P.a * (P.x ^ 9)⁻¹ ≤ sg P K * P.b := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hr0 := F.rpos
  have hr1 : P.x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ F.x1
  have h7 : P.x⁻¹ ^ 7 ≤ 1 := pow_le_one₀ hr0.le hr1
  have h70 : 0 ≤ P.x⁻¹ ^ 7 := pow_nonneg hr0.le 7
  rw [F.ha, ← inv_pow]
  calc 2 * (P.x * P.b) * P.x⁻¹ ^ 9
      = P.b * (2 / 100 * (P.x * P.x⁻¹) * P.x⁻¹ ^ 7) * (100 * z ^ 0 * P.x⁻¹) := by ring
    _ ≤ sg P K * P.b := by
        rw [F.xr]
        exact F.close_sg (by linarith) (by linarith) (F.zr0 0) (F.zr_sg (by norm_num))

/- English proof (authored)
The ninth-power bound controls the coefficient 2a/x⁹ by b times the slope allowance. Multiplication by the nonnegative mT gives the bound in the normalized size unit.
-/
lemma sizeSecond_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tSecondD P m T ≤ sg P K * unitU P m T := by
  unfold tSecondD unitU
  have := scale2 hm hT (size_ninth_power_bound hW hL)
  linarith

/- English proof (authored)
The coefficient a/x⁹ is nonnegative and no larger than 2a/x⁹. The ninth-power estimate bounds the latter by b times the slope allowance. Multiplying by mT yields the index bound.
-/
lemma sizeIo_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tIoD P m T ≤ sg P K * unitU P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have h0 : 0 ≤ P.a * (P.x ^ 9)⁻¹ := mul_nonneg F.apos.le (inv_nonneg.2 (pow_nonneg F.xpos.le 9))
  have key : P.a * (P.x ^ 9)⁻¹ ≤ sg P K * P.b := by
    have := size_ninth_power_bound hW hL
    linarith
  unfold tIoD unitU
  have := scale2 hm hT key
  linarith

/- English proof (authored)
Expand the total size into its eleven contributions. Apply the separate bounds for floors, the auxiliary-prime count, the low and high prime ranges, the order terms, the omitted terms, the band and high terms, the discriminant and the second-prime term. Adding the coefficients gives twice log(4) times the first-prime constant plus thirteen times the slope allowance, all multiplying the common unit.
-/
lemma size_core {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tDetD P m T ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P m T := by
  have a1 := size_floors_bound P e K m T hW hL hm hT
  have a2 := size_cp_bucket_bound P e K m T hW hL hm hT
  have a3 := size_prime_low_bound P e K m T hW hL hm hT
  have a4 := size_prime_high_bound P e K m T hW hL hm hT
  have a5 := size_or_bucket_bound P e K m T hW hL hm hT
  have a6 := sizeOut_core hW hL hm hT
  have a7 := size_orders_bucket_bound P e K m T hW hL hm hT
  have a8 := size_band_bound P e K m T hW hL hm hT
  have a9 := size_high_bucket_bound P e K m T hW hL hm hT
  have a10 := size_discriminant_bound P e K m T hW hL hm hT
  have a11 := sizeSecond_core hW hL hm hT
  unfold tDetD
  linarith

/- English proof (authored)
Take the larger of zero and the constant in the first-kind estimate. The window and large-x assumptions give the auxiliary inequalities, and the nonempty top set ensures that its size is at least one. At any unit, apply the basic loss estimate, then bound the omitted, first-kind and second-kind contributions by their corresponding prime estimates. Their sum is controlled by the total size bound. Separately apply the weighted candidate estimate to the index sum and use the ninth-power size bound. These give the explicit inequalities. Since twice log(4) is at most three, the first-prime constant is nonnegative, and the slope allowance is at most one, the explicit bounds imply the two simpler bounds in the same nonnegative unit.
-/
lemma joint_core : ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → Windows P e K →
    LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
      ExplicitLossAndPrimeLogSumBounds P K Ps cand J TT io D ∧ ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D := by
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  obtain ⟨hTT, hPs, hSig0, hWW, hT2, hio, hAll⟩ := hS
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, -⟩ :=
    side_condition_of_windows P e K hW hL
  have hm : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hT : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hTT
  have hT0 : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ P.a := F.apos.le
  have hU := unitU_nonneg (P := P) hm hT
  have hA : ∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤
      (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P J.card TT.card := by
    intro υ
    obtain ⟨hLed, hFirst, hSecond, hBad⟩ := hAll υ
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
    have led := loss_bound ι κ τ (D υ).W (D υ).below (D υ).l Ps (D υ).cl J TT (D υ).TTp
      (D υ).Iex (D υ).at_ (D υ).wz (D υ).Id (D υ).wd P.d (D υ).gainW (D υ).tauW
      (D υ).gain (D υ).tau (D υ).lo (D υ).fl P.a P.th P.wpp P.Xpp P.Xp P.C P.f P.N P.Sk P.Q₁ P.Q₂
      P.lx P.La P.k P.K₀ (D υ).L₁ P.p₀ l1 (fun p hp => (hPs p hp).1) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
      s11 s12 s13 s14 s15 s16 s17 s18 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    have out := out_discriminant_bound τ Ps PR (D υ).cl TT (D υ).TTp BAD J.card P.a _ hm ha0 hT2 hBad
    have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps (D υ).cl hPs hFirst
      J.card TT.card hm hT0
    have second := second_discriminant_bound Ps cand (D υ).cl Sig P.θ J.card TT.card P.a _ hm hT0 ha0 hSig0 hWW hSecond
    have size := size_core hW hL hm hT
    unfold tDetD tFloors tCp tPrLow tPrHigh tOr tHigh tD tOutD tSecondD at size
    unfold LD.ASK LD.Ga
    linarith
  have hI : ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ sg P K * unitU P J.card TT.card := by
    intro υ
    have h := io_discriminant_bound cand Sig (io υ) P.θ J.card TT.card P.a _ hm hT0 ha0 hWW (hio υ)
    have size := sizeIo_core hW hL hm hT
    unfold tIoD at size
    linarith
  refine ⟨⟨hA, hI⟩, fun υ => (hA υ).trans ?_, fun υ => (hI υ).trans ?_⟩
  · have h1 : 2 * Real.log 4 * P.C + 13 * sg P K ≤ 3 * P.C + 13 := by
      have := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 3 by linarith [log_four_le_three_halves]) F.C0
      linarith [F.sg1]
    exact mul_le_mul_of_nonneg_right h1 hU
  · have := mul_le_mul_of_nonneg_right F.sg1 hU
    linarith

/- English proof (authored)
Use the nonnegative constant furnished by the joint estimate. Set β and the initial scale to zero and transfer the discriminant conditions to the ordinary window conditions by the equivalence. All parameters occurring in the prime constraints and conclusions are preserved by this change. The simpler pair of joint bounds gives the conclusion.
-/
theorem joint_discriminant_bound : LossBoundsUnderSizeWindows := by
  obtain ⟨Cord, h0, h⟩ := joint_core
  refine ⟨Cord, h0, ?_⟩
  intro P e K hC hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  exact (h (clr P) e K hC ((discriminant_windows_iff P e K).1 hW) hL ι κ τ U Ps cand PR J TT BAD Sig io D hS).2

/- English proof (authored)
Keep the nonnegative constant from the joint discriminant bound. For the given ε, e and K, the eventual large-x estimate supplies a threshold above which its hypotheses hold. Substitute the specified value of the parameter ε, and apply the joint bound to each set of windows above the threshold.
-/
theorem joint_discriminant_eventually : LossBoundsEventually := by
  obtain ⟨Cord, h0, h⟩ := joint_discriminant_bound
  refine ⟨Cord, h0, ?_⟩
  intro ε e K hε hε4
  obtain ⟨x₀, hx₀⟩ := large_x_eventually ε e K hε hε4
  refine ⟨x₀, ?_⟩
  intro P hPε hPC hx hW
  exact h P e K hPC hW (by rw [hPε]; exact hx₀ _ hx)

end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
