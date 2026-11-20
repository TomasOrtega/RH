import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.Rounding

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Unfold `lw`. Use `div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)` and prove the remaining obligations. Establish `: Ideal.absNorm w.asIdeal ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot`. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions.
-/
theorem lw_nonneg_here (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K w := by
  unfold lw
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have : Ideal.absNorm w.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/- English proof (translation)
Rewrite using `[← vla_span hx w]`. Conclude with `Nat.cast_nonneg _`.
-/
theorem vAdd_int_nonneg (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) : 0 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]; exact Nat.cast_nonneg _

/- English proof (translation)
Rewrite using `[← vla_span hx w]`. Establish `h0 : Ideal.span {x} ≠ 0`. Rewrite using `[Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hx`. Use `(Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w h0).2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hm))` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem vAdd_int_pos (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) (hm : x ∈ w.asIdeal) :
    1 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]
  have h0 : Ideal.span {x} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  have := (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w h0).2
    (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hm))
  omega

/- English proof (translation)
The claim follows from `(Ideal.finite_factors hI).subset fun w h => by refine (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w hI).1 fun h0 => h ?_ simp [h0]`.
-/
theorem finite_vla {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => (Formalism.L2.Pj.QAt.vla w I : ℝ)).Finite :=
  (Ideal.finite_factors hI).subset fun w h => by
    refine (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w hI).1 fun h0 => h ?_
    simp [h0]

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset (s := (finite_vla hI).toFinset) _ (by simpa using Function.support_mul_subset_left _ _)]`. Establish `h1` using `Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin I hI (finite_vla hI).toFinset fun v hv => by`. Simplify using `using hv`. Rewrite using `[← h1, Finset.sum_div]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [lw, mul_div_assoc]`.
-/
theorem sum_vla_lw {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w I : ℝ) * lw K w = Real.log (Ideal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := (finite_vla hI).toFinset) _
    (by simpa using Function.support_mul_subset_left _ _)]
  have h1 := Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin I hI (finite_vla hI).toFinset fun v hv => by
    simpa using hv
  rw [← h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lw, mul_div_assoc]

/- English proof (translation)
Simplify using `only [vAdd, map_mul]`. Rewrite using `[WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vAdd_mul_here (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  simp only [vAdd, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]; ring

/- English proof (translation)
Simplify using `[vAdd, map_inv₀, WithZero.log_inv]`.
-/
theorem vAdd_inv_here (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd w x⁻¹ = -vAdd w x := by
  simp [vAdd, map_inv₀, WithZero.log_inv]

/- English proof (translation)
Establish `hspan : Ideal.span {c} ≠ ⊥` using `by rwa [Ne, Ideal.span_singleton_eq_bot]`. Establish `hI : ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 hspan`. Rewrite using `[← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton, vAdd_inv_here]`. Establish `h1` using `FractionalIdeal.count_mul K w hI (inv_ne_zero hI)`. Rewrite `h1` using `[mul_inv_cancel₀ hI, FractionalIdeal.count_one]`.

Establish `h2 : FractionalIdeal.count K w ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = vAdd w (algebraMap (𝓞 K) K c)`. Rewrite using `[FractionalIdeal.count_coe K w hspan]`. Conclude with `vla_span hc w`. Use linear arithmetic over natural numbers and integers.
-/
theorem count_inv_span (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K c)⁻¹) =
      vAdd w (algebraMap (𝓞 K) K c)⁻¹ := by
  have hspan : Ideal.span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI : ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hspan
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton, vAdd_inv_here]
  have h1 := FractionalIdeal.count_mul K w hI (inv_ne_zero hI)
  rw [mul_inv_cancel₀ hI, FractionalIdeal.count_one] at h1
  have h2 : FractionalIdeal.count K w ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      vAdd w (algebraMap (𝓞 K) K c) := by
    rw [FractionalIdeal.count_coe K w hspan]
    exact vla_span hc w
  omega

/- English proof (translation)
The claim follows from `(FractionalIdeal.count_coe K w hI).symm`.
-/
theorem vla_eq_count (w : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Formalism.L2.Pj.QAt.vla w I : ℤ) = FractionalIdeal.count K w (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  (FractionalIdeal.count_coe K w hI).symm

/- English proof (translation)
Use `set f : HeightOneSpectrum (𝓞 K) → ℤ := fun w => -⌊ρ w⌋ with hf`. Establish `hfs : Function.support f ⊆ Function.support ρ` using `fun w h h0 => h (by simp [hf, h0])`. Establish `hfin : ∀ᶠ w in Filter.cofinite, f w = 0`. Rewrite using `[Filter.eventually_cofinite]`. Conclude with `hρ.subset hfs`.

Use `set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f w with hJdef`. Establish `hJ0 : J ≠ 0`. Rewrite using `[hJdef, finprod_eq_prod_of_mulSupport_subset (s := hρ.toFinset)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)`. Introduce `w hw`.

Simplify using `only [Set.Finite.coe_toFinset]`. Introduce `h0`. Apply `hw` to reduce the goal to its premises. Simplify using `[hf, h0]`. Establish `hcJ : ∀ w, FractionalIdeal.count K w J = f w` using `fun w => FractionalIdeal.count_finprod K w f hfin`.

Take `⟨c, 𝔞, hc, hJ⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul J`. Use `set a : K := (algebraMap (𝓞 K) K c)⁻¹ with ha`. Establish `ha0 : a ≠ 0` using `inv_ne_zero (by simpa using hc)`. Establish `h𝔞 : 𝔞 ≠ ⊥`. Introduce and unpack `rfl`.

Apply `hJ0` to reduce the goal to its premises. Rewrite using `[hJ]`. Simplify using the standard rewrite rules. Establish `hsa0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0` using `FractionalIdeal.spanSingleton_eq_zero_iff.not.2 ha0`. Establish `h𝔞0 : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h𝔞`.

Establish `hsum : ∀ w, vAdd w a + (Formalism.L2.Pj.QAt.vla w 𝔞 : ℤ) = f w` using `fun w => by`. Rewrite using `[← hcJ w, hJ, FractionalIdeal.count_mul K w hsa0 h𝔞0, vla_eq_count w h𝔞, ha, count_inv_span w hc]`. Use `⟨a, 𝔞, ha0, h𝔞, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb hb0 w`. Establish `hspan : Ideal.span {b} ≠ ⊥` using `by rwa [Ne, Ideal.span_singleton_eq_bot]`.

Take `⟨e, he⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)`. Establish `he0 : e ≠ ⊥` using `by rintro rfl; apply hspan; rw [he]; simp`. Establish `hbK : (b : K) ≠ 0` using `by simpa using hb0`. Establish `h1 : vAdd w ((b : K) * a) = vAdd w (b : K) + vAdd w a` using `vAdd_mul_here w hbK ha0`. Establish `h2 : vAdd w (b : K) = Formalism.L2.Pj.QAt.vla w 𝔞 + Formalism.L2.Pj.QAt.vla w e`.

Rewrite using `[← vla_span hb0 w, vla_eq_count w hspan, vla_eq_count w h𝔞, vla_eq_count w he0, he, FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K w h𝔞0 (FractionalIdeal.coeIdeal_ne_zero.2 he0)]`. Establish `h3 : f w ≤ vAdd w ((b : K) * a)`. Rewrite using `[h1, h2, ← hsum w]`. Use `(Formalism.L2.Pj.QAt.vla w e).zero_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h4 : (f w : ℝ) ≤ vAdd w ((b : K) * a)` using `by exact_mod_cast h3`. Establish `h5` using `Int.fract_nonneg (ρ w)`. Rewrite `h5` using `[Int.fract]`. Simplify using `only [hf, Int.cast_neg] at h4`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e1` using `lineDeg_num ha0`. Unfold `lineDeg at e1`. Establish `e2` using `sum_vla_lw h𝔞`. Establish `e3 : (∑ᶠ w, (vAdd w a : ℝ) * lw K w) + ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w 𝔞 : ℝ) * lw K w = ∑ᶠ w, (f w : ℝ) * lw K w`. Rewrite using `[← finsum_add_distrib (fin_mul (finite_vAdd ha0) _) (fin_mul (finite_vla h𝔞) _)]`.

Use `finsum_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[← add_mul, ← hsum w]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set n : ℕ := ∏ p ∈ B, p with hn`.

Establish `hn0 : n ≠ 0` using `Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero`. Establish `e4 : ∑ p ∈ B, Real.log p = ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w`. Rewrite using `[sum_vAdd_nat hn0, hn, Nat.cast_prod, Real.log_prod]`. Introduce `p hp`. Conclude with `(hB p hp).ne_zero` after adjusting the coercions.

Establish `hfinf : (Function.support fun w => (f w : ℝ) * lw K w).Finite` using `(hρ.subset fun w h h0 => h (by simp [hf, h0]))`. Establish `e5 : (∑ᶠ w, ρ w * lw K w) + ∑ᶠ w, (f w : ℝ) * lw K w ≤ ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w`. Rewrite using `[← finsum_add_distrib (fin_mul hρ _) hfinf]`. Use `finsum_le_finsum' ((fin_mul hρ _).union hfinf |>.subset (Function.support_add _ _)) (fin_mul (finite_vAdd (Nat.cast_ne_zero.2 hn0)) _) fun w => ?_` and prove the remaining obligations. Rewrite using `[← add_mul]`.

Use `mul_le_mul_of_nonneg_right ?_ (lw_nonneg_here w)` and prove the remaining obligations. Establish `hfr : ρ w + (f w : ℝ) = Int.fract (ρ w)` using `by show ρ w + ((-⌊ρ w⌋ : ℤ) : ℝ) = Int.fract (ρ w)`. Rewrite using `[Int.fract, Int.cast_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfr]`.

Establish `hnK : ((n : 𝓞 K) : K) = (n : K)` using `by simp`. Establish `hn0' : (n : 𝓞 K) ≠ 0` using `Nat.cast_ne_zero.2 hn0`. Distinguish the cases in `h : ∃ p ∈ B, ((p : ℕ) : 𝓞 K) ∈ w.asIdeal`. Take `⟨p, hp, hpw⟩` from `h`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun p : ℕ => p) hp`.

Establish `hmem : (n : 𝓞 K) ∈ w.asIdeal`. Rewrite using `[hn, hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hpw`. Establish `h1` using `vAdd_int_pos w hn0' hmem`. Rewrite `h1` using `[hnK]`.

Establish `h2 : (1 : ℝ) ≤ vAdd w (n : K)` using `by exact_mod_cast h1`. Combine the linear relations using `[Int.fract_lt_one (ρ w)]`. Use `push_neg at h`. Take `⟨m, hm⟩` from `hint w h`. Establish `h1` using `vAdd_int_nonneg w hn0'`.

Rewrite `h1` using `[hnK]`. Rewrite using `[hm, Int.fract_intCast]`. Establish `h2 : (0 : ℝ) ≤ (vAdd w (n : K) : ℝ)` using `Int.cast_nonneg h1`. Simplify using `using h2`. Establish `hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ)` using `Nat.cast_pos.2 (Module.finrank_pos (R := ℚ) (M := K))`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_rounding (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hB : ∀ p ∈ B, p.Prime) (hρ : (Function.support ρ).Finite)
    (hint : ∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) :
    ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧
      (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧
      (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤
        -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) -
          Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  set f : HeightOneSpectrum (𝓞 K) → ℤ := fun w => -⌊ρ w⌋ with hf
  have hfs : Function.support f ⊆ Function.support ρ := fun w h h0 => h (by simp [hf, h0])
  have hfin : ∀ᶠ w in Filter.cofinite, f w = 0 := by
    rw [Filter.eventually_cofinite]; exact hρ.subset hfs
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f w with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, finprod_eq_prod_of_mulSupport_subset (s := hρ.toFinset)]
    · exact Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)
    · intro w hw
      simp only [Set.Finite.coe_toFinset]
      intro h0; apply hw; simp [hf, h0]
  have hcJ : ∀ w, FractionalIdeal.count K w J = f w := fun w => FractionalIdeal.count_finprod K w f hfin
  obtain ⟨c, 𝔞, hc, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  set a : K := (algebraMap (𝓞 K) K c)⁻¹ with ha
  have ha0 : a ≠ 0 := inv_ne_zero (by simpa using hc)
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [hJ]; simp
  have hsa0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.2 ha0
  have h𝔞0 : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsum : ∀ w, vAdd w a + (Formalism.L2.Pj.QAt.vla w 𝔞 : ℤ) = f w := fun w => by
    rw [← hcJ w, hJ, FractionalIdeal.count_mul K w hsa0 h𝔞0, vla_eq_count w h𝔞, ha, count_inv_span w hc]
  refine ⟨a, 𝔞, ha0, h𝔞, ?_, ?_⟩
  · intro b hb hb0 w
    have hspan : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨e, he⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
    have he0 : e ≠ ⊥ := by rintro rfl; apply hspan; rw [he]; simp
    have hbK : (b : K) ≠ 0 := by simpa using hb0
    have h1 : vAdd w ((b : K) * a) = vAdd w (b : K) + vAdd w a := vAdd_mul_here w hbK ha0
    have h2 : vAdd w (b : K) = Formalism.L2.Pj.QAt.vla w 𝔞 + Formalism.L2.Pj.QAt.vla w e := by
      rw [← vla_span hb0 w, vla_eq_count w hspan, vla_eq_count w h𝔞, vla_eq_count w he0, he,
        FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K w h𝔞0 (FractionalIdeal.coeIdeal_ne_zero.2 he0)]
    have h3 : f w ≤ vAdd w ((b : K) * a) := by
      rw [h1, h2, ← hsum w]; have := (Formalism.L2.Pj.QAt.vla w e).zero_le; omega
    have h4 : (f w : ℝ) ≤ vAdd w ((b : K) * a) := by exact_mod_cast h3
    have h5 := Int.fract_nonneg (ρ w)
    rw [Int.fract] at h5
    simp only [hf, Int.cast_neg] at h4
    linarith
  · have e1 := lineDeg_num ha0
    unfold lineDeg at e1
    have e2 := sum_vla_lw h𝔞
    have e3 : (∑ᶠ w, (vAdd w a : ℝ) * lw K w) + ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w 𝔞 : ℝ) * lw K w =
        ∑ᶠ w, (f w : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul (finite_vAdd ha0) _) (fin_mul (finite_vla h𝔞) _)]
      refine finsum_congr fun w => ?_
      rw [← add_mul, ← hsum w]; push_cast; ring
    set n : ℕ := ∏ p ∈ B, p with hn
    have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
    have e4 : ∑ p ∈ B, Real.log p = ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [sum_vAdd_nat hn0, hn, Nat.cast_prod, Real.log_prod]
      intro p hp; exact_mod_cast (hB p hp).ne_zero
    have hfinf : (Function.support fun w => (f w : ℝ) * lw K w).Finite :=
      (hρ.subset fun w h h0 => h (by simp [hf, h0]))
    have e5 : (∑ᶠ w, ρ w * lw K w) + ∑ᶠ w, (f w : ℝ) * lw K w ≤ ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul hρ _) hfinf]
      refine finsum_le_finsum' ((fin_mul hρ _).union hfinf |>.subset (Function.support_add _ _))
        (fin_mul (finite_vAdd (Nat.cast_ne_zero.2 hn0)) _) fun w => ?_
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (lw_nonneg_here w)
      have hfr : ρ w + (f w : ℝ) = Int.fract (ρ w) := by
        show ρ w + ((-⌊ρ w⌋ : ℤ) : ℝ) = Int.fract (ρ w)
        rw [Int.fract, Int.cast_neg]; ring
      rw [hfr]
      have hnK : ((n : 𝓞 K) : K) = (n : K) := by simp
      have hn0' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn0
      by_cases h : ∃ p ∈ B, ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
      · obtain ⟨p, hp, hpw⟩ := h
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
        have hmem : (n : 𝓞 K) ∈ w.asIdeal := by
          rw [hn, hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpw
        have h1 := vAdd_int_pos w hn0' hmem
        rw [hnK] at h1
        have h2 : (1 : ℝ) ≤ vAdd w (n : K) := by exact_mod_cast h1
        linarith [Int.fract_lt_one (ρ w)]
      · push_neg at h
        obtain ⟨m, hm⟩ := hint w h
        have h1 := vAdd_int_nonneg w hn0'
        rw [hnK] at h1
        rw [hm, Int.fract_intCast]
        have h2 : (0 : ℝ) ≤ (vAdd w (n : K) : ℝ) := Int.cast_nonneg h1
        simpa using h2
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.2 (Module.finrank_pos (R := ℚ) (M := K))
    linarith

end GlobalTheory.Rounding
