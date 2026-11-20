import Mathlib
import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole
import GroundTheory.GlobalFields.KummerTheory.Splitting

namespace GroundTheory.Global

open NumberField IsDedekindDomain Filter Topology Set Ideal

noncomputable section

section density

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish `h` using `summable_absNorm_rpow_neg (L := K) hs`. Rewrite using `[Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def, tsum_subtype A (fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s)), tsum_subtype B (fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s))]`. Conclude with `Summable.tsum_le_tsum (fun w => indicator_le_indicator_of_subset hAB (fun _ => by positivity) w) (h.indicator A) (h.indicator B)`.
-/
theorem primeIdealZetaSum_mono {A B : Set (HeightOneSpectrum (𝓞 K))} (hAB : A ⊆ B) {s : ℝ}
    (hs : 1 < s) : A.primeIdealZetaSum s ≤ B.primeIdealZetaSum s := by
  have h := summable_absNorm_rpow_neg (L := K) hs
  rw [Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def,
    tsum_subtype A (fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s)),
    tsum_subtype B (fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s))]
  exact Summable.tsum_le_tsum
    (fun w => indicator_le_indicator_of_subset hAB (fun _ => by positivity) w)
    (h.indicator A) (h.indicator B)

/- English proof (translation)
Simplify using `only [Set.primeIdealZetaSum_def]`. Conclude with `Summable.tsum_union_disjoint (f := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s)) hd (summable_absNorm_rpow_neg_subtype A hs) (summable_absNorm_rpow_neg_subtype B hs)`.
-/
theorem primeIdealZetaSum_union {A B : Set (HeightOneSpectrum (𝓞 K))} (hd : Disjoint A B)
    {s : ℝ} (hs : 1 < s) :
    (A ∪ B).primeIdealZetaSum s = A.primeIdealZetaSum s + B.primeIdealZetaSum s := by
  simp only [Set.primeIdealZetaSum_def]
  exact Summable.tsum_union_disjoint
    (f := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s)) hd
    (summable_absNorm_rpow_neg_subtype A hs) (summable_absNorm_rpow_neg_subtype B hs)

/- English proof (translation)
Take `⟨C, hC⟩` from `hS`. Establish `hC' : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s ≤ C` using `eventually_map.mp hC`. Establish `hden` using `tendsto_primeIdealZetaSum_univ_atTop K`. Establish `hpos` using `hden.eventually_gt_atTop 0`. Unfold `Set.HasDirichletDensity`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (Tendsto.div_atTop (tendsto_const_nhds (x := C)) hden) (Eventually.of_forall fun s => ?_) ?_` and prove the remaining obligations. Conclude with `div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)`. Use `filter_upwards [hC', hpos] with s h1 h2`. Conclude with `div_le_div_of_nonneg_right h1 h2.le`.
-/
theorem hasDirichletDensity_zero_of_isBoundedUnder {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => S.primeIdealZetaSum s) :
    S.HasDirichletDensity 0 := by
  obtain ⟨C, hC⟩ := hS
  have hC' : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s ≤ C := eventually_map.mp hC
  have hden := tendsto_primeIdealZetaSum_univ_atTop K
  have hpos := hden.eventually_gt_atTop 0
  unfold Set.HasDirichletDensity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Tendsto.div_atTop (tendsto_const_nhds (x := C)) hden) (Eventually.of_forall fun s => ?_) ?_
  · exact div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [hC', hpos] with s h1 h2
    exact div_le_div_of_nonneg_right h1 h2.le

/- English proof (translation)
Unfold `Set.HasDirichletDensity`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [(tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0] with s hs`. Conclude with `(div_self hs.ne').symm`.
-/
theorem hasDirichletDensity_univ : (univ : Set (HeightOneSpectrum (𝓞 K))).HasDirichletDensity 1 := by
  unfold Set.HasDirichletDensity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm

/- English proof (translation)
Establish `h0` using `hasDirichletDensity_zero_of_isBoundedUnder hb`. Unfold `Set.HasDirichletDensity at h0 ⊢`. Establish `heq : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s = T.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s + (S \ T).primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZet …` using `by filter_upwards [self_mem_nhdsWithin] with s hs`. Rewrite using `[← add_div, ← primeIdealZetaSum_union disjoint_sdiff_right hs, union_sdiff_cancel hTS]`. Prove the components needed by the constructor for the conclusion.

Introduce `hT`. Use `hT.add h0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `this.congr' (heq.mono fun s hs => hs.symm)`. Introduce `hS`.

Use `hS.sub h0` as an intermediate fact. Rewrite `this` using `[sub_zero]`. Use `this.congr' (heq.mono fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDirichletDensity_iff_of_subset_of_isBoundedUnder {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hTS : T ⊆ S) (hb : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => (S \ T).primeIdealZetaSum s)
    (δ : ℝ) : T.HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  have h0 := hasDirichletDensity_zero_of_isBoundedUnder hb
  unfold Set.HasDirichletDensity at h0 ⊢
  have heq : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      S.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
        T.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s +
        (S \ T).primeIdealZetaSum s /
          (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← add_div, ← primeIdealZetaSum_union disjoint_sdiff_right hs, union_sdiff_cancel hTS]
  constructor
  · intro hT
    have := hT.add h0
    rw [add_zero] at this
    exact this.congr' (heq.mono fun s hs => hs.symm)
  · intro hS
    have := hS.sub h0
    rw [sub_zero] at this
    refine this.congr' (heq.mono fun s hs => ?_)
    rw [hs]
    ring

end density

section degreeOne

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in

/- English proof (translation)
The claim follows from `hasDirichletDensity_zero_of_isBoundedUnder (isBoundedUnder_primeIdealZetaSum_higherDegreePrimes K L)`.
-/
theorem hasDirichletDensity_higherDegreePrimes :
    (higherDegreePrimes K L).HasDirichletDensity 0 :=
  hasDirichletDensity_zero_of_isBoundedUnder
    (isBoundedUnder_primeIdealZetaSum_higherDegreePrimes K L)

variable (K) in

/- English proof (translation)
Use `hasDirichletDensity_iff_of_subset_of_isBoundedUnder inter_subset_left ?_ δ` and prove the remaining obligations. Take `⟨C, hC⟩` from `primeIdealZetaSum_higherDegreePrimes_le K L`. Use `isBoundedUnder_of_eventually_le (a := C) (eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_)` and prove the remaining obligations. Use `(primeIdealZetaSum_mono ?_ hs).trans (hC s hs.le)` and prove the remaining obligations. Introduce `w hw`.

Rewrite using `[← compl_degreeOnePrimes]`. Conclude with `fun h => hw.2 ⟨hw.1, h⟩`.
-/
theorem hasDirichletDensity_inter_degreeOnePrimes_iff (S : Set (HeightOneSpectrum (𝓞 L)))
    (δ : ℝ) : (S ∩ degreeOnePrimes K L).HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  refine hasDirichletDensity_iff_of_subset_of_isBoundedUnder inter_subset_left ?_ δ
  obtain ⟨C, hC⟩ := primeIdealZetaSum_higherDegreePrimes_le K L
  refine isBoundedUnder_of_eventually_le (a := C)
    (eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_)
  refine (primeIdealZetaSum_mono ?_ hs).trans (hC s hs.le)
  intro w hw
  rw [← compl_degreeOnePrimes]
  exact fun h => hw.2 ⟨hw.1, h⟩

variable (K L) in

/- English proof (translation)
Use `(hasDirichletDensity_inter_degreeOnePrimes_iff K univ 1).mpr (hasDirichletDensity_univ (K := L))` as an intermediate fact. Rewrite `this` using `[univ_inter]`. Then use the resulting hypothesis.
-/
theorem hasDirichletDensity_degreeOnePrimes : (degreeOnePrimes K L).HasDirichletDensity 1 := by
  have := (hasDirichletDensity_inter_degreeOnePrimes_iff K univ 1).mpr
    (hasDirichletDensity_univ (K := L))
  rwa [univ_inter] at this

end degreeOne

section asymptotic

variable (K : Type*) [Field K] [NumberField K]

/- English proof (translation)
Establish `h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0)`. Use `tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => show 0 < s - 1 by linarith⟩` and prove the remaining obligations. Establish `: Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0)`. Simplify using `using (continuous_sub_right (1 : ℝ)).tendsto 1`. Conclude with `this.mono_left nhdsWithin_le_nhds`.

Conclude with `tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)`.
-/
theorem tendsto_neg_log_sub_one_atTop :
    Tendsto (fun s : ℝ => -Real.log (s - 1)) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨?_, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => show 0 < s - 1 by linarith⟩
    have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
      simpa using (continuous_sub_right (1 : ℝ)).tendsto 1
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_abs_primeIdealZetaSum_add_log_le K`. Establish `hu` using `tendsto_neg_log_sub_one_atTop`. Establish `hupos` using `hu.eventually_gt_atTop 0`. Use `set P := fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s`. Establish `h0 : Tendsto (fun s : ℝ => (P s + Real.log (s - 1)) / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0)`.

Establish `hlo : Tendsto (fun s : ℝ => -C / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0)` using `Tendsto.div_atTop (tendsto_const_nhds (x := -C)) hu`. Establish `hhi : Tendsto (fun s : ℝ => C / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0)` using `Tendsto.div_atTop (tendsto_const_nhds (x := C)) hu`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hC, hupos] with s h1 h2`. Conclude with `div_le_div_of_nonneg_right (abs_le.mp h1).1 h2.le`.

Use `filter_upwards [hC, hupos] with s h1 h2`. Conclude with `div_le_div_of_nonneg_right (abs_le.mp h1).2 h2.le`. Use `h0.const_add 1` as an intermediate fact. Rewrite `this` using `[add_zero]`. Use `this.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [hupos] with s hs`. Establish `hne : -Real.log (s - 1) ≠ 0` using `hs.ne'`. Simplify using `only [P]`. Rewrite using `[eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_primeIdealZetaSum_univ_div_neg_log :
    Tendsto (fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s /
      -Real.log (s - 1)) (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_add_log_le K
  have hu := tendsto_neg_log_sub_one_atTop
  have hupos := hu.eventually_gt_atTop 0
  set P := fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s
  have h0 : Tendsto (fun s : ℝ => (P s + Real.log (s - 1)) / -Real.log (s - 1)) (𝓝[>] 1)
      (𝓝 0) := by
    have hlo : Tendsto (fun s : ℝ => -C / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) :=
      Tendsto.div_atTop (tendsto_const_nhds (x := -C)) hu
    have hhi : Tendsto (fun s : ℝ => C / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) :=
      Tendsto.div_atTop (tendsto_const_nhds (x := C)) hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hC, hupos] with s h1 h2
      exact div_le_div_of_nonneg_right (abs_le.mp h1).1 h2.le
    · filter_upwards [hC, hupos] with s h1 h2
      exact div_le_div_of_nonneg_right (abs_le.mp h1).2 h2.le
  have := h0.const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hupos] with s hs
  have hne : -Real.log (s - 1) ≠ 0 := hs.ne'
  simp only [P]
  rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  ring

/- English proof (translation)
Establish `h` using `(tendsto_primeIdealZetaSum_univ_div_neg_log K).div (tendsto_primeIdealZetaSum_univ_div_neg_log L) one_ne_zero`. Rewrite `h` using `[div_one]`. Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards [tendsto_neg_log_sub_one_atTop.eventually_gt_atTop 0] with s hs`. Conclude with `div_div_div_cancel_right₀ hs.ne' _ _`.
-/
theorem tendsto_primeIdealZetaSum_univ_div_univ (L : Type*) [Field L] [NumberField L] :
    Tendsto (fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s /
      (univ : Set (HeightOneSpectrum (𝓞 L))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 1) := by
  have h := (tendsto_primeIdealZetaSum_univ_div_neg_log K).div
    (tendsto_primeIdealZetaSum_univ_div_neg_log L) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [tendsto_neg_log_sub_one_atTop.eventually_gt_atTop 0] with s hs
  exact div_div_div_cancel_right₀ hs.ne' _ _

end asymptotic

section split

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Set `_` to `Fintype.ofFinite (v.asIdeal.primesOver (𝓞 L))`. Establish `hsum : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) = Module.finrank K L`. Rewrite using `[Ideal.sum_ramification_inertia_eq_finrank, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]`. Establish `key : (v.asIdeal.primesOver (𝓞 L)).ncard = ∑ _q : v.asIdeal.primesOver (𝓞 L), 1`. Rewrite using `[← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]`.

Rewrite using `[key, ← hsum, Finset.sum_eq_sum_iff_of_le (fun q _ => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 (𝓞 K)).ne' (Ideal.inertiaDeg_pos q.1 (𝓞 K)).ne'))]`. Prove the components needed by the constructor for the conclusion. Introduce `h q _`. Establish `hq0 : q.1 ≠ ⊥` using `Ideal.ne_bot_of_mem_primesOver v.ne_bot q.2`. Use `h ⟨q.1, q.2.1, hq0⟩ q.2.2` as an intermediate fact.

Rewrite using `[this.1, this.2]`. Introduce `h w hw`. Use `h ⟨w.asIdeal, w.isPrime, hw⟩ (Finset.mem_univ _)` as an intermediate fact. Conclude with `mul_eq_one.mp this.symm`.
-/
theorem splitsCompletely_iff_ncard_primesOver (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely L v ↔ (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  classical
  let _ := Fintype.ofFinite (v.asIdeal.primesOver (𝓞 L))
  have hsum : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  have key : (v.asIdeal.primesOver (𝓞 L)).ncard = ∑ _q : v.asIdeal.primesOver (𝓞 L), 1 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  rw [key, ← hsum, Finset.sum_eq_sum_iff_of_le (fun q _ => Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 (𝓞 K)).ne'
      (Ideal.inertiaDeg_pos q.1 (𝓞 K)).ne'))]
  constructor
  · intro h q _
    have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot q.2
    have := h ⟨q.1, q.2.1, hq0⟩ q.2.2
    rw [this.1, this.2]
  · intro h w hw
    have := h ⟨w.asIdeal, w.isPrime, hw⟩ (Finset.mem_univ _)
    exact mul_eq_one.mp this.symm

/- English proof (translation)
The claim follows from `(splitsCompletely_iff_ncard_primesOver L v).mp hv`.
-/
theorem ncard_primesOver_of_splitsCompletely {v : HeightOneSpectrum (𝓞 K)}
    (hv : SplitsCompletely L v) : (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L :=
  (splitsCompletely_iff_ncard_primesOver L v).mp hv

/- English proof (translation)
Establish `: IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L)` using `IsGaloisGroup.of_isFractionRing _ _ _ K L`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h w hw`. Introduce and unpack `⟨he, hf⟩ w' hw'`.

Rewrite using `[Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(L/K), Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(L/K)]`. Conclude with `⟨he, hf⟩`.
-/
theorem splitsCompletely_iff_of_isGalois [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [hw : w.asIdeal.LiesOver v.asIdeal] :
    SplitsCompletely L v ↔
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  constructor
  · intro h
    exact h w hw
  · rintro ⟨he, hf⟩ w' hw'
    rw [Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(L/K),
      Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(L/K)]
    exact ⟨he, hf⟩

def primesAbove (T : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | w.under (𝓞 K) ∈ T}

end split

section relation

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

/- English proof (translation)
Set `π : primesAbove L T → T` to `fun w => ⟨w.1.under (𝓞 K), w.2⟩`. Establish `hlies : ∀ (v : T) (w : {w // π w = v}), w.1.1.asIdeal.LiesOver v.1.asIdeal`. Introduce `v w`. Use `⟨?_⟩` and prove the remaining obligations. Use `congrArg (fun x : T => x.1.asIdeal) w.2` as an intermediate fact.

Conclude with `this.symm`. Establish `hnorm : ∀ (v : T) (w : {w // π w = v}), (absNorm w.1.1.asIdeal : ℝ) ^ (-s) = (absNorm v.1.asIdeal : ℝ) ^ (-s)`. Introduce `v w`. Use `hlies v w` as an intermediate fact. Establish `hf` using `(hT v.1 v.2 w.1.1 this).2`.

Rewrite using `[← Ideal.absNorm_pow_inertiaDeg v.1.asIdeal w.1.1.asIdeal, hf, pow_one]`. Establish `hcard : ∀ v : T, Nat.card {w // π w = v} = Module.finrank K L`. Introduce `v`. Rewrite using `[← ncard_primesOver_of_splitsCompletely L (hT v.1 v.2), ← Nat.card_coe_set_eq]`. Use `Nat.card_eq_of_bijective (fun w => (⟨w.1.1.asIdeal, w.1.1.isPrime, hlies v w⟩ : v.1.asIdeal.primesOver (𝓞 L))) ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `a b h`. Conclude with `Subtype.ext (Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)))`. Introduce `q`. Establish `hq0 : q.1 ≠ ⊥` using `Ideal.ne_bot_of_mem_primesOver v.1.ne_bot q.2`. Establish `hu : (⟨q.1, q.2.1, hq0⟩ : HeightOneSpectrum (𝓞 L)).under (𝓞 K) = v.1` using `HeightOneSpectrum.ext q.2.2.over.symm`.

Establish `hmem : (⟨q.1, q.2.1, hq0⟩ : HeightOneSpectrum (𝓞 L)) ∈ primesAbove L T` using `by show HeightOneSpectrum.under (𝓞 K) ⟨q.1, q.2.1, hq0⟩ ∈ T`. Rewrite using `[hu]`. Conclude with `v.2`. Conclude with `⟨⟨⟨⟨q.1, q.2.1, hq0⟩, hmem⟩, Subtype.ext hu⟩, rfl⟩`. Establish `hfin : ∀ v : T, Finite {w // π w = v}` using `fun v => Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')`.

Establish `hsumL` using `summable_absNorm_rpow_neg_subtype (primesAbove L T) hs`. Rewrite using `[Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def, ← (Equiv.sigmaFiberEquiv π).tsum_eq, Summable.tsum_sigma' (f := fun p => (absNorm ((Equiv.sigmaFiberEquiv π) p).1.asIdeal : ℝ) ^ (-s)) (fun v => by have := hfin v; exact Summable.of_finite) ((Equiv.sigmaFiberEquiv π).summable …`. Use `tsum_congr fun v => ?_` and prove the remaining obligations. Use `hfin v` as an intermediate fact. Set `_` to `Fintype.ofFinite {w // π w = v}`.

Rewrite using `[tsum_fintype]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]`.
-/
theorem primeIdealZetaSum_primesAbove {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, SplitsCompletely L v) {s : ℝ} (hs : 1 < s) :
    (primesAbove L T).primeIdealZetaSum s = Module.finrank K L * T.primeIdealZetaSum s := by
  classical
  let π : primesAbove L T → T := fun w => ⟨w.1.under (𝓞 K), w.2⟩
  have hlies : ∀ (v : T) (w : {w // π w = v}), w.1.1.asIdeal.LiesOver v.1.asIdeal := by
    intro v w
    refine ⟨?_⟩
    have := congrArg (fun x : T => x.1.asIdeal) w.2
    exact this.symm
  have hnorm : ∀ (v : T) (w : {w // π w = v}),
      (absNorm w.1.1.asIdeal : ℝ) ^ (-s) = (absNorm v.1.asIdeal : ℝ) ^ (-s) := by
    intro v w
    have := hlies v w
    have hf := (hT v.1 v.2 w.1.1 this).2
    rw [← Ideal.absNorm_pow_inertiaDeg v.1.asIdeal w.1.1.asIdeal, hf, pow_one]
  have hcard : ∀ v : T, Nat.card {w // π w = v} = Module.finrank K L := by
    intro v
    rw [← ncard_primesOver_of_splitsCompletely L (hT v.1 v.2), ← Nat.card_coe_set_eq]
    refine Nat.card_eq_of_bijective
      (fun w => (⟨w.1.1.asIdeal, w.1.1.isPrime, hlies v w⟩ : v.1.asIdeal.primesOver (𝓞 L)))
      ⟨?_, ?_⟩
    · intro a b h
      exact Subtype.ext (Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)))
    · intro q
      have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.1.ne_bot q.2
      have hu : (⟨q.1, q.2.1, hq0⟩ : HeightOneSpectrum (𝓞 L)).under (𝓞 K) = v.1 :=
        HeightOneSpectrum.ext q.2.2.over.symm
      have hmem : (⟨q.1, q.2.1, hq0⟩ : HeightOneSpectrum (𝓞 L)) ∈ primesAbove L T := by
        show HeightOneSpectrum.under (𝓞 K) ⟨q.1, q.2.1, hq0⟩ ∈ T
        rw [hu]
        exact v.2
      exact ⟨⟨⟨⟨q.1, q.2.1, hq0⟩, hmem⟩, Subtype.ext hu⟩, rfl⟩
  have hfin : ∀ v : T, Finite {w // π w = v} := fun v =>
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  have hsumL := summable_absNorm_rpow_neg_subtype (primesAbove L T) hs
  rw [Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def,
    ← (Equiv.sigmaFiberEquiv π).tsum_eq,
    Summable.tsum_sigma'
      (f := fun p => (absNorm ((Equiv.sigmaFiberEquiv π) p).1.asIdeal : ℝ) ^ (-s))
      (fun v => by have := hfin v; exact Summable.of_finite)
      ((Equiv.sigmaFiberEquiv π).summable_iff.mpr hsumL :),
    ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  have := hfin v
  let _ := Fintype.ofFinite {w // π w = v}
  rw [tsum_fintype]
  calc ∑ w : {w // π w = v}, (absNorm (Equiv.sigmaFiberEquiv π ⟨v, w⟩).1.asIdeal : ℝ) ^ (-s)
      = ∑ _w : {w // π w = v}, (absNorm v.1.asIdeal : ℝ) ^ (-s) :=
        Finset.sum_congr rfl fun w _ => hnorm v w
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

/- English proof (translation)
Use `set n : ℝ := (Module.finrank K L : ℝ) with hndef`. Establish `hn : n ≠ 0`. Rewrite using `[hndef]`. Conclude with `(Module.finrank_pos (R := K) (M := L)).ne'` after adjusting the coercions. Establish `hKL` using `tendsto_primeIdealZetaSum_univ_div_univ K L`.

Establish `hLK` using `tendsto_primeIdealZetaSum_univ_div_univ L K`. Establish `hKpos` using `(tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0`. Establish `hLpos` using `(tendsto_primeIdealZetaSum_univ_atTop L).eventually_gt_atTop 0`. Unfold `Set.HasDirichletDensity`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `(h.const_mul n⁻¹).mul hLK` as an intermediate fact. Rewrite `this` using `[mul_one, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]`. Use `this.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, hKpos, hLpos] with s hs hK hL`.

Establish `hK'` using `hK.ne'`. Establish `hL'` using `hL.ne'`. Rewrite using `[primeIdealZetaSum_primesAbove hT hs]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hndef]`.

Apply the tactic sequence `try ring`. Introduce `h`. Use `(h.const_mul n).mul hKL` as an intermediate fact. Rewrite `this` using `[mul_one]`. Use `this.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin, hKpos, hLpos] with s hs hK hL`. Establish `hK'` using `hK.ne'`. Establish `hL'` using `hL.ne'`. Rewrite using `[primeIdealZetaSum_primesAbove hT hs]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hndef]`. Apply the tactic sequence `try ring`.
-/
theorem hasDirichletDensity_primesAbove_iff {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, SplitsCompletely L v) (δ : ℝ) :
    (primesAbove L T).HasDirichletDensity (Module.finrank K L * δ) ↔ T.HasDirichletDensity δ := by
  set n : ℝ := (Module.finrank K L : ℝ) with hndef
  have hn : n ≠ 0 := by
    rw [hndef]
    exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
  have hKL := tendsto_primeIdealZetaSum_univ_div_univ K L
  have hLK := tendsto_primeIdealZetaSum_univ_div_univ L K
  have hKpos := (tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0
  have hLpos := (tendsto_primeIdealZetaSum_univ_atTop L).eventually_gt_atTop 0
  unfold Set.HasDirichletDensity
  constructor
  · intro h
    have := (h.const_mul n⁻¹).mul hLK
    rw [mul_one, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hKpos, hLpos] with s hs hK hL
    have hK' := hK.ne'
    have hL' := hL.ne'
    rw [primeIdealZetaSum_primesAbove hT hs]
    field_simp
    rw [hndef]
    try ring
  · intro h
    have := (h.const_mul n).mul hKL
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hKpos, hLpos] with s hs hK hL
    have hK' := hK.ne'
    have hL' := hL.ne'
    rw [primeIdealZetaSum_primesAbove hT hs]
    field_simp
    rw [hndef]
    try ring

end relation

section chebotarevSplit

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

/- English proof (translation)
The claim follows from `isBoundedUnder_of_eventually_le (a := S.ncard) (eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => Set.primeIdealZetaSum_le_card_of_finite hS (by linarith))`.
-/
theorem isBoundedUnder_primeIdealZetaSum_of_finite {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => S.primeIdealZetaSum s :=
  isBoundedUnder_of_eventually_le (a := S.ncard) (eventually_nhdsWithin_of_forall
    fun s (hs : 1 < s) => Set.primeIdealZetaSum_le_card_of_finite hS (by linarith))

/- English proof (translation)
The claim follows from `hasDirichletDensity_zero_of_isBoundedUnder (isBoundedUnder_primeIdealZetaSum_of_finite hS)`.
-/
theorem hasDirichletDensity_zero_of_finite {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) : S.HasDirichletDensity 0 :=
  hasDirichletDensity_zero_of_isBoundedUnder (isBoundedUnder_primeIdealZetaSum_of_finite hS)

/- English proof (translation)
Establish `h2 : 2 ≤ w.asIdeal.ramificationIdx (𝓞 K)`. Use `Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set v := w.asIdeal.under (𝓞 K)`. Establish `hv0 : v ≠ ⊥` using `mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot`.

Establish `: v.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hv0`. Establish `hmap : v.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥` using `(Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hv0`. Establish `he` using `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v w.asIdeal hmap`. Establish `hdvd : w.asIdeal ^ w.asIdeal.ramificationIdx (𝓞 K) ∣ v.map (algebraMap (𝓞 K) (𝓞 L))`. Rewrite using `[he]`.

Conclude with `pow_multiplicity_dvd _ _`. Use `pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L w.asIdeal (by omega) hv0 hdvd` as an intermediate fact. Conclude with `(dvd_pow_self _ (by omega)).trans this`.
-/
theorem dvd_differentIdeal_of_ramificationIdx_ne_one {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1) :
    w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have h2 : 2 ≤ w.asIdeal.ramificationIdx (𝓞 K) := by
    have := Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)
    omega
  set v := w.asIdeal.under (𝓞 K)
  have hv0 : v ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot
  have : v.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hv0
  have hmap : v.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hv0
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v w.asIdeal hmap
  have hdvd : w.asIdeal ^ w.asIdeal.ramificationIdx (𝓞 K) ∣
      v.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [he]
    exact pow_multiplicity_dvd _ _
  have := pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L w.asIdeal (by omega) hv0 hdvd
  exact (dvd_pow_self _ (by omega)).trans this

variable (K L) in

/- English proof (translation)
The claim follows from `(Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset fun _ hw => dvd_differentIdeal_of_ramificationIdx_ne_one hw`.
-/
theorem finite_setOf_ramificationIdx_ne_one :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun _ hw => dvd_differentIdeal_of_ramificationIdx_ne_one hw

variable (K L) in

/- English proof (translation)
Use `set Spl := {v : HeightOneSpectrum (𝓞 K) | SplitsCompletely L v}`. Establish `hT : ∀ v ∈ Spl, SplitsCompletely L v` using `fun v hv => hv`. Establish `hsub : primesAbove L Spl ⊆ degreeOnePrimes K L`. Introduce `w hw`. Establish `hlies : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`.

Conclude with `(hT _ hw w hlies).2`. Establish `hdiff : degreeOnePrimes K L \ primesAbove L Spl ⊆ {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}`. Introduce and unpack `w ⟨hw1, hw2⟩ he`. Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Conclude with `hw2 ((splitsCompletely_iff_of_isGalois L (w.under (𝓞 K)) w).mpr ⟨he, hw1⟩)`.

Establish `h1 : (primesAbove L Spl).HasDirichletDensity 1` using `(hasDirichletDensity_iff_of_subset_of_isBoundedUnder hsub (isBoundedUnder_primeIdealZetaSum_of_finite ((finite_setOf_ramificationIdx_ne_one K L).subset hdiff)) 1).mpr (hasDirichletDensity_degreeOnePrimes K L)`. Establish `hn : (Module.finrank K L : ℝ) ≠ 0`. Conclude with `(Module.finrank_pos (R := K) (M := L)).ne'` after adjusting the coercions. Use `(hasDirichletDensity_primesAbove_iff hT _).mp ?_` and prove the remaining obligations. Rewrite using `[mul_one_div_cancel hn]` and apply the resulting hypothesis.
-/
theorem hasDirichletDensity_setOf_splitsCompletely [IsGalois K L] :
    {v : HeightOneSpectrum (𝓞 K) | SplitsCompletely L v}.HasDirichletDensity
      (1 / Module.finrank K L) := by
  set Spl := {v : HeightOneSpectrum (𝓞 K) | SplitsCompletely L v}
  have hT : ∀ v ∈ Spl, SplitsCompletely L v := fun v hv => hv
  have hsub : primesAbove L Spl ⊆ degreeOnePrimes K L := by
    intro w hw
    have hlies : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    exact (hT _ hw w hlies).2
  have hdiff : degreeOnePrimes K L \ primesAbove L Spl ⊆
      {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1} := by
    rintro w ⟨hw1, hw2⟩ he
    have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    exact hw2 ((splitsCompletely_iff_of_isGalois L (w.under (𝓞 K)) w).mpr ⟨he, hw1⟩)
  have h1 : (primesAbove L Spl).HasDirichletDensity 1 :=
    (hasDirichletDensity_iff_of_subset_of_isBoundedUnder hsub
      (isBoundedUnder_primeIdealZetaSum_of_finite
        ((finite_setOf_ramificationIdx_ne_one K L).subset hdiff)) 1).mpr
      (hasDirichletDensity_degreeOnePrimes K L)
  have hn : (Module.finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
  refine (hasDirichletDensity_primesAbove_iff hT _).mp ?_
  rwa [mul_one_div_cancel hn]

end chebotarevSplit

end

end GroundTheory.Global
