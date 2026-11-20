import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

noncomputable def idealZetaR (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)

/- English proof (translation)
Use `⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ E).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]`. Reduce the equality to equality of the corresponding arguments. Rewrite using `[← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one, show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _, show 1 = Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = 0} by`. Simplify using `[Ideal.absNorm_eq_zero_iff],`.

Use the proof step `Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),`. Use the proof step `← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]`. Simplify using `[Set.coe_eq_subtype]`.
-/
theorem idealZetaR_tendsto_sum_card_div (E : Type) [Field E] [NumberField E] :
    ∃ c : ℝ, Tendsto (fun n : ℕ ↦
    (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ)) / n)
      atTop (𝓝 c) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ E).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[LSeries.term, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]`. Rewrite using `[LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem idealZetaR_term_eq (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv]
    push_cast
    rfl

/- English proof (translation)
Take `⟨c, hc⟩` from `idealZetaR_tendsto_sum_card_div E`. Establish `hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ)`. Repeatedly rewrite using `[Real.rpow_one]`. Use `Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hc` and prove the remaining obligations. Use `filter_upwards [eventually_ne_atTop 0] with n hn h`.

Conclude with `absurd h (Nat.cast_ne_zero.mpr hn)`. Use `LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (s : ℂ)) (by simpa using hs)` as an intermediate fact. Unfold `LSeriesSummable at this`. Establish `h2` using `(funext (idealZetaR_term_eq E (zero_lt_one.trans hs)))`. Simplify using `only [Complex.ofReal_natCast] at this h2`.

Rewrite `this` using `[h2]`. Conclude with `Complex.summable_ofReal.mp this`.
-/
theorem summable_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  obtain ⟨c, hc⟩ := idealZetaR_tendsto_sum_card_div E
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    simp_rw [Real.rpow_one]
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hc
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd h (Nat.cast_ne_zero.mpr hn)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (s := (s : ℂ)) (by simpa using hs)
  unfold LSeriesSummable at this
  have h2 := (funext (idealZetaR_term_eq E (zero_lt_one.trans hs)))
  simp only [Complex.ofReal_natCast] at this h2
  rw [h2] at this
  exact Complex.summable_ofReal.mp this

/- English proof (translation)
Unfold `dedekindZeta LSeries idealZetaR`. Rewrite using `[Complex.ofReal_tsum]`. Conclude with `tsum_congr fun n ↦ idealZetaR_term_eq E (zero_lt_one.trans hs) n`.
-/
theorem dedekindZeta_eq_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E (s : ℂ) = ((idealZetaR E s : ℝ) : ℂ) := by
  unfold dedekindZeta LSeries idealZetaR
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ idealZetaR_term_eq E (zero_lt_one.trans hs) n

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := Ideal.absNorm) (t := T.image Ideal.absNorm) (fun I hI ↦ Finset.mem_image_of_mem _ hI)]`. Use `le_trans ?_ ((summable_idealZetaR E hs).sum_le_tsum (T.image Ideal.absNorm) (fun n _ ↦ by positivity))` and prove the remaining obligations. Use `Finset.sum_le_sum fun n _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s)) (fun I hI ↦ by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul]`. Establish `hfin` using `Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n`.

Establish `hc : Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} = hfin.toFinset.card` using `Nat.card_eq_card_finite_toFinset hfin`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[hc, Nat.cast_le]`. Use `Finset.card_le_card fun I hI ↦ ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter] at hI`.

Simplify using `using hI.2`.
-/
theorem sum_le_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s)
    (T : Finset (Ideal (𝓞 E))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤ idealZetaR E s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Ideal.absNorm) (t := T.image Ideal.absNorm)
    (fun I hI ↦ Finset.mem_image_of_mem _ hI)]
  refine le_trans ?_ ((summable_idealZetaR E hs).sum_le_tsum (T.image Ideal.absNorm)
    (fun n _ ↦ by positivity))
  refine Finset.sum_le_sum fun n _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s))
    (fun I hI ↦ by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul]
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n
  have hc : Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} = hfin.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hfin
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [hc, Nat.cast_le]
  refine Finset.card_le_card fun I hI ↦ ?_
  simp only [Finset.mem_filter] at hI
  simpa using hI.2

/- English proof (translation)
The claim follows from `summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ sum_le_idealZetaR E hs u`.
-/
theorem summable_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) :=
  summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ sum_le_idealZetaR E hs u

/- English proof (translation)
Establish `hsum` using `(summable_absNorm_rpow_ideal E hs).hasSum`. Establish `h1` using `((Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ)).hasSum_iff).mpr hsum`. Establish `h2` using `h1.sigma (g := fun n : ℕ => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) (fun n ↦ by`. Establish `: Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n}` using `(Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype`. Establish `hc : ∀ c : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}, ((Ideal.absNorm (Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ) ⟨n, c⟩) : ℕ) : ℝ) ^ (-s) = (n : ℝ) ^ (-s)` using `fun c ↦ by`.

Simplify using `[Equiv.sigmaFiberEquiv, c.2]`. Simplify using `only [Function.comp_apply, hc]`. Establish `h3 : HasSum (fun _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n} ↦ (n : ℝ) ^ (-s)) (∑' _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}, (n : ℝ) ^ (-s))` using `Summable.of_finite.hasSum`. Rewrite `h3` using `[tsum_const, nsmul_eq_mul]`. Conclude with `h3)`.

Rewrite using `[idealZetaR, h2.tsum_eq]`. Conclude with `hsum`.
-/
theorem hasSum_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    HasSum (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) (idealZetaR E s) := by
  have hsum := (summable_absNorm_rpow_ideal E hs).hasSum
  have h1 := ((Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ)).hasSum_iff).mpr hsum
  have h2 := h1.sigma (g := fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) (fun n ↦ by
    have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
    have hc : ∀ c : {I : Ideal (𝓞 E) // Ideal.absNorm I = n},
        ((Ideal.absNorm (Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ) ⟨n, c⟩) : ℕ) : ℝ)
          ^ (-s) = (n : ℝ) ^ (-s) := fun c ↦ by
      simp [Equiv.sigmaFiberEquiv, c.2]
    simp only [Function.comp_apply, hc]
    have h3 : HasSum (fun _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n} ↦ (n : ℝ) ^ (-s))
        (∑' _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}, (n : ℝ) ^ (-s)) :=
      Summable.of_finite.hasSum
    rw [tsum_const, nsmul_eq_mul] at h3
    exact h3)
  rw [idealZetaR, h2.tsum_eq]
  exact hsum

/- English proof (translation)
The claim follows from `(summable_absNorm_rpow_ideal E hs).subtype _`.
-/
theorem summable_absNorm_rpow (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)) :=
  (summable_absNorm_rpow_ideal E hs).subtype _

/- English proof (translation)
Establish `hsupp : Function.support (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) ⊆ {a | a ≠ ⊥}`. Introduce `a ha hbot`. Apply `ha` to reduce the goal to its premises. Establish `hb : a = ⊥` using `by simpa using hbot`. Simplify using `[hb, Real.zero_rpow (neg_ne_zero.mpr (zero_lt_one.trans hs).ne')]`.

Establish `h1 : ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) = idealZetaR E s`. Rewrite using `[← (hasSum_absNorm_rpow_ideal E hs).tsum_eq]`. Conclude with `tsum_subtype_eq_of_support_subset hsupp`. Rewrite using `[dedekindZeta_eq_idealZetaR E hs, ← h1, Complex.ofReal_tsum]`. Use `tsum_congr fun a ↦ ?_` and prove the remaining obligations.

Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]`.
-/
theorem dedekindZeta_eq_tsum (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E s = ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  have hsupp : Function.support (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) ⊆
      {a | a ≠ ⊥} := by
    intro a ha hbot
    apply ha
    have hb : a = ⊥ := by simpa using hbot
    simp [hb, Real.zero_rpow (neg_ne_zero.mpr (zero_lt_one.trans hs).ne')]
  have h1 : ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) = idealZetaR E s := by
    rw [← (hasSum_absNorm_rpow_ideal E hs).tsum_eq]
    exact tsum_subtype_eq_of_support_subset hsupp
  rw [dedekindZeta_eq_idealZetaR E hs, ← h1, Complex.ofReal_tsum]
  refine tsum_congr fun a ↦ ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]

/- English proof (translation)
Establish `h0 : Ideal.absNorm q.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `q.ne_bot`. Establish `h1 : Ideal.absNorm q.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `q.isPrime.ne_top`. Unfold `Nrm`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_Nrm {E : Type} [Field E] [NumberField E] (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Ideal.absNorm q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  have h1 : Ideal.absNorm q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact q.isPrime.ne_top
  unfold Nrm
  omega

/- English proof (translation)
Use `summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ ?_` and prove the remaining obligations. Unfold `Nrm`. Rewrite using `[← Finset.sum_image (f := fun I : Ideal (𝓞 E) ↦ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s)) (g := IsDedekindDomain.HeightOneSpectrum.asIdeal) (fun v _ w _ h ↦ IsDedekindDomain.HeightOneSpectrum.ext h)]`. Conclude with `sum_le_idealZetaR E hs _`.
-/
theorem summable_prm_rpow (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) := by
  classical
  refine summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ ?_
  unfold Nrm
  rw [← Finset.sum_image (f := fun I : Ideal (𝓞 E) ↦ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s))
    (g := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    (fun v _ w _ h ↦ IsDedekindDomain.HeightOneSpectrum.ext h)]
  exact sum_le_idealZetaR E hs _

end ReciprocityTheory.Cheb
