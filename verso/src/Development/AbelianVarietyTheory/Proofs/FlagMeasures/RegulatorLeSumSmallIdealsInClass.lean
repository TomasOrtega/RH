import Mathlib
import Formalism.HermitianLattices.StatementMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeSumVolumeOfCover
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumePosSimplexLe

open MeasureTheory NumberField Finset

namespace GlobalTheory.RegulatorClassBound

open NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open scoped nonZeroDivisors

/- English proof (translation)
Use `set n := finrank ℚ K with hn_def`. Establish `hn : 0 < n` using `finrank_pos`. Establish `hN : 0 < (Ideal.absNorm I : ℝ)` using `Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_of_ne_zero (by simpa using hI)))`. Establish `hD : 0 < Real.sqrt |(discr K : ℝ)|` using `Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))`. Use `set X : ℝ := (Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)| with hX_def`.

Establish `hX : 0 < X` using `mul_pos hN hD`. Set `J : (FractionalIdeal (𝓞 K)⁰ K)ˣ` to `Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)`. Set `f : InfinitePlace K → NNReal` to `fun w => ⟨Real.exp (c w), (Real.exp_pos _).le⟩`. Establish `hL : (minkowskiBound K J).toReal = (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n`. Repeatedly rewrite using `[minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]`.

Rewrite using `[ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]`. Simplify using `only [J, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hV : volume (convexBodyLT K f) ≠ ⊤`. Rewrite using `[convexBodyLT_volume]`.

Conclude with `ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top`. Establish `hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * X`. Rewrite using `[convexBodyLT_volume, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]`. Use `congr 1`. Rewrite using `[NNReal.coe_prod]`.

Establish `e : ∀ x : InfinitePlace K, ((f x ^ x.mult : NNReal) : ℝ) = Real.exp (x.mult * c x)` using `fun x => by rw [NNReal.coe_pow, Real.exp_nat_mul]; rfl`. Rewrite using `[Finset.prod_congr rfl fun x _ => e x, ← Real.exp_sum, hc, Real.exp_log hX]`. Establish `hfin : n = 2 * nrComplexPlaces K` using `IsTotallyComplex.finrank K`. Establish `hr : nrRealPlaces K = 0` using `IsTotallyComplex.nrRealPlaces_eq_zero K`. Establish `h : minkowskiBound K J < volume (convexBodyLT K f)`.

Rewrite using `[← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR']`. Establish `h1 : (convexBodyLTFactor K : ℝ) = Real.pi ^ nrComplexPlaces K`. Simplify using `[convexBodyLTFactor, hr]`. Establish `h3 : (2 : ℝ) ^ nrComplexPlaces K < Real.pi ^ nrComplexPlaces K` using `pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) (by omega)`. Establish `h4 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n = 2 ^ nrComplexPlaces K`.

Rewrite using `[hfin, pow_mul, ← mul_pow]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h4, h1]`. Conclude with `mul_lt_mul_of_pos_right h3 hX`.

Take `⟨a, ha, hne, hlt⟩` from `exists_ne_zero_mem_ideal_lt K J h`. Rewrite `ha` using `[Units.val_mk0, FractionalIdeal.mem_coeIdeal]`. Take `⟨x, hx, rfl⟩` from `ha`. Use `⟨x, hx, fun h0 => hne (by rw [h0, map_zero]), fun w => ?_⟩` and prove the remaining obligations. Conclude with `hlt w`.
-/
theorem exists_mem_box (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (c : InfinitePlace K → ℝ)
    (hc : ∑ w, (w.mult : ℝ) * c w = Real.log ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|)) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ w : InfinitePlace K, w (a : K) < Real.exp (c w) := by
  classical
  set n := finrank ℚ K with hn_def
  have hn : 0 < n := finrank_pos
  have hN : 0 < (Ideal.absNorm I : ℝ) :=
    Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2
      (mem_nonZeroDivisors_of_ne_zero (by simpa using hI)))
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  set X : ℝ := (Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)| with hX_def
  have hX : 0 < X := mul_pos hN hD
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
  let f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (c w), (Real.exp_pos _).le⟩
  have hL : (minkowskiBound K J).toReal =
      (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n := by
    simp_rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]
    rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
    simp only [J, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Real.coe_sqrt,
      coe_nnnorm, Int.norm_eq_abs]
    ring
  have hV : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * X := by
    rw [convexBodyLT_volume, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
    congr 1
    rw [NNReal.coe_prod]
    have e : ∀ x : InfinitePlace K, ((f x ^ x.mult : NNReal) : ℝ) = Real.exp (x.mult * c x) :=
      fun x => by rw [NNReal.coe_pow, Real.exp_nat_mul]; rfl
    rw [Finset.prod_congr rfl fun x _ => e x, ← Real.exp_sum, hc, Real.exp_log hX]
  have hfin : n = 2 * nrComplexPlaces K := IsTotallyComplex.finrank K
  have hr : nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR']
    have h1 : (convexBodyLTFactor K : ℝ) = Real.pi ^ nrComplexPlaces K := by
      simp [convexBodyLTFactor, hr]
    have h3 : (2 : ℝ) ^ nrComplexPlaces K < Real.pi ^ nrComplexPlaces K :=
      pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) (by omega)
    have h4 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n = 2 ^ nrComplexPlaces K := by
      rw [hfin, pow_mul, ← mul_pow]; norm_num
    calc (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n
        = ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n) * X := by rw [hX_def]; ring
      _ < (convexBodyLTFactor K : ℝ) * X := by
        rw [h4, h1]; exact mul_lt_mul_of_pos_right h3 hX
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt K J h
  rw [Units.val_mk0, FractionalIdeal.mem_coeIdeal] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨x, hx, fun h0 => hne (by rw [h0, map_zero]), fun w => ?_⟩
  exact hlt w

/- English proof (translation)
Establish `ha' : (a : K) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 ha`. Establish `h` using `prod_eq_abs_norm (a : K)`. Establish `h2 : (Ideal.absNorm (Ideal.span {a}) : ℝ) = ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ)`. Rewrite using `[Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[h2, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (pos_iff.2 ha').ne')]`. Simplify using `[Real.log_pow]`.
-/
theorem sum_mult_log (K : Type) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (a : K)) =
      Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  have ha' : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  have h := prod_eq_abs_norm (a : K)
  have h2 : (Ideal.absNorm (Ideal.span {a}) : ℝ) = ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) := by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast; rfl
  rw [h2, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (pos_iff.2 ha').ne')]
  simp [Real.log_pow]

/- English proof (translation)
Introduce `K _ _ hK C S hS`. Use `set Y := Real.sqrt |(discr K : ℝ)| with hY`. Establish `hD : 0 < Y` using `Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))`. Take `⟨⟨J, hJ⟩, hJC⟩` from `ClassGroup.mk0_surjective C⁻¹`. Establish `hJ0 : J ≠ ⊥` using `nonZeroDivisors.ne_zero hJ`.

Establish `hpos : ∀ I : Ideal (𝓞 K), I ∈ (Ideal (𝓞 K))⁰ → 0 < (Ideal.absNorm I : ℝ)` using `fun I hI => Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 hI)`. Establish `hgen : ∀ I : Ideal (𝓞 K), ∃ y : 𝓞 K, (∃ x : 𝓞 K, Ideal.span {x} = J * I) → Ideal.span {y} = J * I`. Introduce `I`. Distinguish the cases in `h : ∃ x : 𝓞 K, Ideal.span {x} = J * I`. Take `⟨x, hx⟩` from `h`.

Conclude with `⟨x, fun _ => hx⟩`. Conclude with `⟨0, fun h' => absurd h' h⟩`. Use `choose y hy using hgen`. Set `a : Ideal (𝓞 K) → logSpace K` to `fun I w => (w.1.mult : ℝ) * Real.log (w.1 (y I : K))`. Set `A : Ideal (𝓞 K) → Set (logSpace K)` to `fun I => {t | (∀ i, a I i ≤ t i) ∧ ∑ i, (t i - a I i) ≤ Real.log (Y / Ideal.absNorm I)}`.

Establish `hL : ∀ I ∈ S, 0 ≤ Real.log (Y / Ideal.absNorm I)`. Introduce `I hI`. Take `⟨h1, -, h2⟩` from `(hS I).1 hI`. Conclude with `Real.log_nonneg ((one_le_div (hpos I h1)).2 h2)`. Establish `hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = Units.rank K`.

Simplify using `[Units.rank]`. Establish `hmeas : ∀ I, MeasurableSet (A I)`. Introduce `I`. Use `IsClosed.measurableSet ?_` and prove the remaining obligations. Establish `h1 : IsClosed {t : logSpace K | ∀ i, a I i ≤ t i}`.

Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)`. Conclude with `h1.inter (isClosed_le (f := fun t : logSpace K => ∑ i, (t i - a I i)) (by fun_prop) continuous_const)`. Establish `hcov : ∀ t : logSpace K, ∃ I ∈ S, ∃ l ∈ unitLattice K, t + l ∈ A I`. Introduce `t`.

Set `b : InfinitePlace K → ℝ` to `fun w => if h : w = w₀ then Real.log ((Ideal.absNorm J : ℝ) * Y) - ∑ i, t i else t ⟨w, h⟩`. Establish `hb : ∀ i : {w : InfinitePlace K // w ≠ w₀}, b i.1 = t i` using `fun i => dif_neg i.2`. Establish `hbsum : ∑ w, b w = Real.log ((Ideal.absNorm J : ℝ) * Y)`. Rewrite using `[Fintype.sum_eq_add_sum_subtype_ne _ w₀]`. Simplify using `only [hb]`.

Simplify using `[b]`. Establish `hm : ∀ w : InfinitePlace K, (0 : ℝ) < w.mult` using `fun w => Nat.cast_pos.2 mult_pos`. Establish `hbc : ∀ w : InfinitePlace K, (w.mult : ℝ) * (b w / w.mult) = b w` using `fun w => mul_div_cancel₀ _ (hm w).ne'`. Take `⟨x, hxJ, hx0, hx⟩` from `exists_mem_box K J hJ0 (fun w => b w / w.mult) (by simp only [hbc]; exact hbsum)`. Establish `hx0' : (x : K) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 hx0`.

Establish `hs : ∀ w : InfinitePlace K, 0 ≤ b w - (w.mult : ℝ) * Real.log (w (x : K))`. Introduce `w`. Establish `h1 : Real.log (w (x : K)) ≤ b w / w.mult` using `(Real.log_le_iff_le_exp (pos_iff.2 hx0')).2 (hx w).le`. Use `mul_le_mul_of_nonneg_left h1 (hm w).le` as an intermediate fact. Rewrite `this` using `[hbc]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨I, hI⟩ : J ∣ Ideal.span {x}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxJ)`. Establish `hI0 : I ∈ (Ideal (𝓞 K))⁰`. Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Introduce and unpack `rfl`.

Rewrite `hI` using `[mul_zero]`. Conclude with `hx0 (Ideal.span_singleton_eq_bot.1 hI)`. Establish `hsum : ∑ w : InfinitePlace K, (b w - (w.mult : ℝ) * Real.log (w (x : K))) = Real.log (Y / Ideal.absNorm I)`. Rewrite using `[Finset.sum_sub_distrib, hbsum, sum_mult_log K x hx0, hI, map_mul, Nat.cast_mul, Real.log_mul (hpos J hJ).ne' hD.ne', Real.log_mul (hpos J hJ).ne' (hpos I hI0).ne', Real.log_div hD.ne' (hpos I hI0).ne']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hIS : I ∈ S`. Use `(hS I).2 ⟨hI0, ?_, ?_⟩` and prove the remaining obligations. Establish `: ClassGroup.mk0 ⟨J, hJ⟩ = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹` using `ClassGroup.mk0_eq_mk0_inv_iff.2 ⟨x, hx0, hI.symm⟩`. Rewrite `this` using `[hJC]`. Conclude with `(inv_injective this).symm`.

Establish `h0 : 0 ≤ Real.log (Y / Ideal.absNorm I)` using `hsum ▸ Finset.sum_nonneg fun w _ => hs w`. Use `(Real.log_nonneg_iff (div_pos hD (hpos I hI0))).1 h0` as an intermediate fact. Conclude with `(one_le_div (hpos I hI0)).1 this`. Establish `hyI : Ideal.span {x} = Ideal.span {y I}` using `hI.trans (hy I ⟨x, hI⟩).symm`. Take `⟨u, hu⟩` from `Ideal.span_singleton_eq_span_singleton.1 hyI`.

Establish `key : ∀ i : {w : InfinitePlace K // w ≠ w₀}, (t + logEmbedding K (Additive.ofMul u)) i - a I i = b i.1 - (i.1.mult : ℝ) * Real.log (i.1 (x : K))`. Introduce `i`. Establish `h1 : ((y I : 𝓞 K) : K) = (x : K) * ((u : 𝓞 K) : K)`. Rewrite using `[← hu]`. Simplify using the standard rewrite rules.

Simplify using `only [a, Pi.add_apply, logEmbedding_component, hb, h1, map_mul]`. Rewrite using `[Real.log_mul (pos_iff.2 hx0').ne' (Units.pos_at_place u i.1).ne']`. Expand and normalize the polynomial expressions, which then agree. Use `⟨I, hIS, logEmbedding K (Additive.ofMul u), ⟨Additive.ofMul u, trivial, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `hs i.1` as an intermediate fact. Rewrite `this` using `[← key]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [key]`. Rewrite using `[← hsum, Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)]`.

Combine the linear relations using `[hs w₀]`. Establish `h1` using `GlobalTheory.covolume_le_sum_volume_of_cover _ (unitLattice K) _ S A hmeas hcov`. Establish `h2 : ∑ I ∈ S, volume (A I) ≤ ∑ I ∈ S, ENNReal.ofReal (Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ))`. Use `Finset.sum_le_sum fun I hI => ?_` and prove the remaining obligations. Use `GlobalTheory.SimplexVolume.volume_simplex_le _ (a I) _ (hL I hI)` as an intermediate fact.

Rewrite `this` using `[hcard]`. Conclude with `this`. Establish `hnn : ∀ I ∈ S, 0 ≤ Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)` using `fun I hI => div_nonneg (pow_nonneg (hL I hI) _) (Nat.cast_nonneg _)`. Rewrite `h2` using `[← ENNReal.ofReal_sum_of_nonneg hnn]`. Conclude with `(ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)).1 (h1.trans h2)`.
-/
theorem regulator_le_sum_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by
  intro K _ _ hK C S hS
  classical
  set Y := Real.sqrt |(discr K : ℝ)| with hY
  have hD : 0 < Y := Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  obtain ⟨⟨J, hJ⟩, hJC⟩ := ClassGroup.mk0_surjective C⁻¹
  have hJ0 : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ
  have hpos : ∀ I : Ideal (𝓞 K), I ∈ (Ideal (𝓞 K))⁰ → 0 < (Ideal.absNorm I : ℝ) := fun I hI =>
    Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 hI)
  have hgen : ∀ I : Ideal (𝓞 K), ∃ y : 𝓞 K,
      (∃ x : 𝓞 K, Ideal.span {x} = J * I) → Ideal.span {y} = J * I := by
    intro I
    by_cases h : ∃ x : 𝓞 K, Ideal.span {x} = J * I
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hgen
  let a : Ideal (𝓞 K) → logSpace K := fun I w => (w.1.mult : ℝ) * Real.log (w.1 (y I : K))
  let A : Ideal (𝓞 K) → Set (logSpace K) := fun I =>
    {t | (∀ i, a I i ≤ t i) ∧ ∑ i, (t i - a I i) ≤ Real.log (Y / Ideal.absNorm I)}
  have hL : ∀ I ∈ S, 0 ≤ Real.log (Y / Ideal.absNorm I) := by
    intro I hI
    obtain ⟨h1, -, h2⟩ := (hS I).1 hI
    exact Real.log_nonneg ((one_le_div (hpos I h1)).2 h2)
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = Units.rank K := by
    simp [Units.rank]
  have hmeas : ∀ I, MeasurableSet (A I) := by
    intro I
    refine IsClosed.measurableSet ?_
    have h1 : IsClosed {t : logSpace K | ∀ i, a I i ≤ t i} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact h1.inter (isClosed_le (f := fun t : logSpace K => ∑ i, (t i - a I i))
      (by fun_prop) continuous_const)
  have hcov : ∀ t : logSpace K, ∃ I ∈ S, ∃ l ∈ unitLattice K, t + l ∈ A I := by
    intro t
    let b : InfinitePlace K → ℝ := fun w =>
      if h : w = w₀ then Real.log ((Ideal.absNorm J : ℝ) * Y) - ∑ i, t i else t ⟨w, h⟩
    have hb : ∀ i : {w : InfinitePlace K // w ≠ w₀}, b i.1 = t i := fun i => dif_neg i.2
    have hbsum : ∑ w, b w = Real.log ((Ideal.absNorm J : ℝ) * Y) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
      simp only [hb]
      simp [b]
    have hm : ∀ w : InfinitePlace K, (0 : ℝ) < w.mult := fun w => Nat.cast_pos.2 mult_pos
    have hbc : ∀ w : InfinitePlace K, (w.mult : ℝ) * (b w / w.mult) = b w := fun w =>
      mul_div_cancel₀ _ (hm w).ne'
    obtain ⟨x, hxJ, hx0, hx⟩ := exists_mem_box K J hJ0 (fun w => b w / w.mult)
      (by simp only [hbc]; exact hbsum)
    have hx0' : (x : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hx0
    have hs : ∀ w : InfinitePlace K, 0 ≤ b w - (w.mult : ℝ) * Real.log (w (x : K)) := by
      intro w
      have h1 : Real.log (w (x : K)) ≤ b w / w.mult :=
        (Real.log_le_iff_le_exp (pos_iff.2 hx0')).2 (hx w).le
      have := mul_le_mul_of_nonneg_left h1 (hm w).le
      rw [hbc] at this
      linarith
    obtain ⟨I, hI⟩ : J ∣ Ideal.span {x} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxJ)
    have hI0 : I ∈ (Ideal (𝓞 K))⁰ := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rintro rfl
      rw [mul_zero] at hI
      exact hx0 (Ideal.span_singleton_eq_bot.1 hI)
    have hsum : ∑ w : InfinitePlace K, (b w - (w.mult : ℝ) * Real.log (w (x : K))) =
        Real.log (Y / Ideal.absNorm I) := by
      rw [Finset.sum_sub_distrib, hbsum, sum_mult_log K x hx0, hI, map_mul, Nat.cast_mul,
        Real.log_mul (hpos J hJ).ne' hD.ne', Real.log_mul (hpos J hJ).ne' (hpos I hI0).ne',
        Real.log_div hD.ne' (hpos I hI0).ne']
      ring
    have hIS : I ∈ S := by
      refine (hS I).2 ⟨hI0, ?_, ?_⟩
      · have : ClassGroup.mk0 ⟨J, hJ⟩ = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ :=
          ClassGroup.mk0_eq_mk0_inv_iff.2 ⟨x, hx0, hI.symm⟩
        rw [hJC] at this
        exact (inv_injective this).symm
      · have h0 : 0 ≤ Real.log (Y / Ideal.absNorm I) :=
          hsum ▸ Finset.sum_nonneg fun w _ => hs w
        have := (Real.log_nonneg_iff (div_pos hD (hpos I hI0))).1 h0
        exact (one_le_div (hpos I hI0)).1 this
    have hyI : Ideal.span {x} = Ideal.span {y I} := hI.trans (hy I ⟨x, hI⟩).symm
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 hyI
    have key : ∀ i : {w : InfinitePlace K // w ≠ w₀},
        (t + logEmbedding K (Additive.ofMul u)) i - a I i =
          b i.1 - (i.1.mult : ℝ) * Real.log (i.1 (x : K)) := by
      intro i
      have h1 : ((y I : 𝓞 K) : K) = (x : K) * ((u : 𝓞 K) : K) := by
        rw [← hu]; simp
      simp only [a, Pi.add_apply, logEmbedding_component, hb, h1, map_mul]
      rw [Real.log_mul (pos_iff.2 hx0').ne' (Units.pos_at_place u i.1).ne']
      ring
    refine ⟨I, hIS, logEmbedding K (Additive.ofMul u), ⟨Additive.ofMul u, trivial, rfl⟩, ?_, ?_⟩
    · intro i
      have := hs i.1
      rw [← key] at this
      linarith
    · simp only [key]
      rw [← hsum, Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)]
      linarith [hs w₀]
  have h1 := GlobalTheory.covolume_le_sum_volume_of_cover _ (unitLattice K) _ S A hmeas hcov
  have h2 : ∑ I ∈ S, volume (A I) ≤ ∑ I ∈ S, ENNReal.ofReal
      (Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)) := by
    refine Finset.sum_le_sum fun I hI => ?_
    have := GlobalTheory.SimplexVolume.volume_simplex_le _ (a I) _ (hL I hI)
    rw [hcard] at this
    exact this
  have hnn : ∀ I ∈ S, 0 ≤
      Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) :=
    fun I hI => div_nonneg (pow_nonneg (hL I hI) _) (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)).1 (h1.trans h2)

end GlobalTheory.RegulatorClassBound
