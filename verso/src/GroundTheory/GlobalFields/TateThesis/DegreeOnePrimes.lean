import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain Filter Topology Set

noncomputable section

/- English proof (translation)
Set `_` to `Fintype.ofFinite (p.primesOver S)`. Rewrite using `[← Ideal.sum_ramification_inertia_eq_finrank p S, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]`. Use `Finset.sum_le_sum fun q _ => ?_` and prove the remaining obligations. Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 R).ne' (Ideal.inertiaDeg_pos q.1 R).ne')`.
-/
theorem card_primesOver_le_finrank {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime]
    [Finite (p.primesOver S)] :
    Nat.card (p.primesOver S) ≤ Module.finrank R S := by
  classical
  let _ := Fintype.ofFinite (p.primesOver S)
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S, Nat.card_eq_fintype_card,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 R).ne' (Ideal.inertiaDeg_pos q.1 R).ne')

variable {K L : Type*} [Field L] [NumberField L]

def rationalPrimeUnder (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  Ideal.absNorm (w.asIdeal.under ℤ)

omit [NumberField L] in
/- English proof (translation)
The claim follows from `mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot`.
-/
theorem under_int_ne_bot (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.under ℤ ≠ ⊥ :=
  mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

omit [NumberField L] in

/- English proof (translation)
The claim follows from `(Int.prime_absNorm _).mpr (Ideal.prime_of_isPrime (under_int_ne_bot w) inferInstance)`.
-/
theorem rationalPrimeUnder_prime (w : HeightOneSpectrum (𝓞 L)) : (rationalPrimeUnder w).Prime :=
  (Int.prime_absNorm _).mpr (Ideal.prime_of_isPrime (under_int_ne_bot w) inferInstance)

omit [NumberField L] in

/- English proof (translation)
The claim follows from `Int.ideal_span_absNorm_eq_self _`.
-/
theorem span_rationalPrimeUnder (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.span {((rationalPrimeUnder w : ℕ) : ℤ)} = w.asIdeal.under ℤ :=
  Int.ideal_span_absNorm_eq_self _

/- English proof (translation)
The claim follows from `(Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under ℤ) w.asIdeal).symm`.
-/
theorem absNorm_eq_rationalPrimeUnder_pow (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm w.asIdeal = rationalPrimeUnder w ^ w.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under ℤ) w.asIdeal).symm

/- English proof (translation)
Rewrite using `[absNorm_eq_rationalPrimeUnder_pow]`. Conclude with `Nat.le_self_pow (Ideal.inertiaDeg_pos w.asIdeal ℤ).ne' _`.
-/
theorem rationalPrimeUnder_le_absNorm (w : HeightOneSpectrum (𝓞 L)) :
    rationalPrimeUnder w ≤ Ideal.absNorm w.asIdeal := by
  rw [absNorm_eq_rationalPrimeUnder_pow]
  exact Nat.le_self_pow (Ideal.inertiaDeg_pos w.asIdeal ℤ).ne' _

/- English proof (translation)
Establish `hf` using `Ideal.inertiaDeg_pos w.asIdeal ℤ`. Rewrite `hw`, the goal using `[absNorm_eq_rationalPrimeUnder_pow]`. Establish `hf1 : w.asIdeal.inertiaDeg ℤ ≠ 1`. Introduce `h`. Rewrite `hw` using `[h, pow_one]`.

Conclude with `hw (rationalPrimeUnder_prime w)`. Conclude with `Nat.pow_le_pow_right (rationalPrimeUnder_prime w).pos (by omega)`.
-/
theorem sq_rationalPrimeUnder_le_absNorm {w : HeightOneSpectrum (𝓞 L)}
    (hw : ¬ (Ideal.absNorm w.asIdeal).Prime) :
    rationalPrimeUnder w ^ 2 ≤ Ideal.absNorm w.asIdeal := by
  have hf := Ideal.inertiaDeg_pos w.asIdeal ℤ
  rw [absNorm_eq_rationalPrimeUnder_pow] at hw ⊢
  have hf1 : w.asIdeal.inertiaDeg ℤ ≠ 1 := by
    intro h
    rw [h, pow_one] at hw
    exact hw (rationalPrimeUnder_prime w)
  exact Nat.pow_le_pow_right (rationalPrimeUnder_prime w).pos (by omega)

/- English proof (translation)
Break down `isEmpty_or_nonempty {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} with h | h` into its components or cases. Conclude with `⟨inferInstance, by simp⟩`. Take `⟨w₀⟩` from `h`. Use `set P := w₀.1.asIdeal.under ℤ with hPdef`. Establish `: P.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance (under_int_ne_bot w₀.1)`.

Establish `: Finite (P.primesOver (𝓞 L))` using `(IsDedekindDomain.primesOver_finite P (𝓞 L)).to_subtype`. Establish `hP : ∀ w : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n}, w.1.asIdeal.under ℤ = P`. Introduce `w`. Rewrite using `[hPdef, ← span_rationalPrimeUnder, ← span_rationalPrimeUnder, w.2, w₀.2]`. Set `f : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} → P.primesOver (𝓞 L)` to `fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(hP w).symm⟩⟩`.

Establish `hf : Function.Injective f`. Introduce `a b hab`. Conclude with `Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val hab))`. Conclude with `⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans (card_primesOver_le_finrank P)⟩`.
-/
theorem finite_and_card_fiber_rationalPrimeUnder_le (n : ℕ) :
    Finite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ∧
      Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} ≤
        Module.finrank ℤ (𝓞 L) := by
  rcases isEmpty_or_nonempty {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} with h | h
  · exact ⟨inferInstance, by simp⟩
  obtain ⟨w₀⟩ := h
  set P := w₀.1.asIdeal.under ℤ with hPdef
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (under_int_ne_bot w₀.1)
  have : Finite (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).to_subtype
  have hP : ∀ w : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n},
      w.1.asIdeal.under ℤ = P := by
    intro w
    rw [hPdef, ← span_rationalPrimeUnder, ← span_rationalPrimeUnder, w.2, w₀.2]
  let f : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} → P.primesOver (𝓞 L) :=
    fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(hP w).symm⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val hab))
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans (card_primesOver_le_finrank P)⟩

/- English proof (translation)
Rewrite using `[← (Equiv.sigmaFiberEquiv (rationalPrimeUnder (L := L))).summable_iff]`. Use `(summable_sigma_of_nonneg (f := fun x => g (Equiv.sigmaFiberEquiv (rationalPrimeUnder (L := L)) x)) (fun _ => hg _)).mpr ⟨fun n => ?_, ?_⟩` and prove the remaining obligations. Use `(finite_and_card_fiber_rationalPrimeUnder_le (L := L) n).1` as an intermediate fact. Conclude with `Summable.of_finite`. Use `Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => hg _) (fun n => ?_) (hh.mul_left ((Module.finrank ℤ (𝓞 L) : ℕ) : ℝ))` and prove the remaining obligations.

Take `⟨hfin, hcard⟩` from `finite_and_card_fiber_rationalPrimeUnder_le (L := L) n`. Set `_` to `Fintype.ofFinite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n}`. Rewrite using `[tsum_fintype]`. Combine the equalities or inequalities in the displayed calculation. Simplify `hgh y.1` using `[Equiv.sigmaFiberEquiv, y.2]`.

Use `_ = (Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} : ℝ) * h n := by`. Simplify using `[Nat.card_eq_fintype_card]`. Use `_ ≤ (Module.finrank ℤ (𝓞 L) : ℝ) * h n := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hh0 n)`.
-/
theorem summable_of_le_rationalPrimeUnder (g : HeightOneSpectrum (𝓞 L) → ℝ) {h : ℕ → ℝ}
    (hg : ∀ w, 0 ≤ g w) (hh0 : ∀ n, 0 ≤ h n) (hh : Summable h)
    (hgh : ∀ w, g w ≤ h (rationalPrimeUnder w)) : Summable g := by
  classical
  rw [← (Equiv.sigmaFiberEquiv (rationalPrimeUnder (L := L))).summable_iff]
  refine (summable_sigma_of_nonneg
    (f := fun x => g (Equiv.sigmaFiberEquiv (rationalPrimeUnder (L := L)) x))
    (fun _ => hg _)).mpr ⟨fun n => ?_, ?_⟩
  · have := (finite_and_card_fiber_rationalPrimeUnder_le (L := L) n).1
    exact Summable.of_finite
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => hg _) (fun n => ?_)
    (hh.mul_left ((Module.finrank ℤ (𝓞 L) : ℕ) : ℝ))
  obtain ⟨hfin, hcard⟩ := finite_and_card_fiber_rationalPrimeUnder_le (L := L) n
  let _ := Fintype.ofFinite {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n}
  rw [tsum_fintype]
  calc ∑ y : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n},
        g (Equiv.sigmaFiberEquiv rationalPrimeUnder ⟨n, y⟩)
      ≤ ∑ _y : {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n}, h n :=
        Finset.sum_le_sum fun y _ => by
          simpa [Equiv.sigmaFiberEquiv, y.2] using hgh y.1
    _ = (Nat.card {w : HeightOneSpectrum (𝓞 L) // rationalPrimeUnder w = n} : ℝ) * h n := by
        simp [Nat.card_eq_fintype_card]
    _ ≤ (Module.finrank ℤ (𝓞 L) : ℝ) * h n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hh0 n)

/- English proof (translation)
The claim follows from `(rationalPrimeUnder_prime w).one_le.trans (rationalPrimeUnder_le_absNorm w)`.
-/
theorem one_le_absNorm (w : HeightOneSpectrum (𝓞 L)) : 1 ≤ Ideal.absNorm w.asIdeal :=
  (rationalPrimeUnder_prime w).one_le.trans (rationalPrimeUnder_le_absNorm w)

/- English proof (translation)
Use `summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-s)) (fun _ => by positivity) (fun _ => by positivity) (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (rationalPrimeUnder_prime w).pos) (by exact_mod_cast rationalPrimeUnder_le_absNorm w) (by linarith)`.
-/
theorem summable_absNorm_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) := by
  refine summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-s))
    (fun _ => by positivity) (fun _ => by positivity)
    (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (rationalPrimeUnder_prime w).pos)
    (by exact_mod_cast rationalPrimeUnder_le_absNorm w) (by linarith)

/- English proof (translation)
Use `(summable_subtype_iff_indicator (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}) (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_` and prove the remaining obligations. Use `summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-(2 * s))) (fun _ => Set.indicator_nonneg (fun _ _ => by positivity) _) (fun _ => by positivity) (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}`. Rewrite using `[Set.indicator_of_mem hw]`. Establish `hp : (0 : ℝ) < rationalPrimeUnder w` using `by exact_mod_cast (rationalPrimeUnder_prime w).pos`.

Establish `hle : ((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ)`. Rewrite using `[Real.rpow_two]`. Conclude with `sq_rationalPrimeUnder_le_absNorm hw` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hp.le]`.

Put the polynomial expressions in normal form. Rewrite using `[Set.indicator_of_notMem hw]`. Check the signs of the components of the expression.
-/
theorem summable_absNorm_rpow_neg_of_not_prime {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : {w : HeightOneSpectrum (𝓞 L) // ¬ (Ideal.absNorm w.asIdeal).Prime} =>
      (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by
  refine (summable_subtype_iff_indicator
    (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime})
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_
  refine summable_of_le_rationalPrimeUnder _ (h := fun n : ℕ => (n : ℝ) ^ (-(2 * s)))
    (fun _ => Set.indicator_nonneg (fun _ _ => by positivity) _) (fun _ => by positivity)
    (Real.summable_nat_rpow.mpr (by linarith)) (fun w => ?_)
  by_cases hw : w ∈ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}
  · rw [Set.indicator_of_mem hw]
    have hp : (0 : ℝ) < rationalPrimeUnder w := by exact_mod_cast (rationalPrimeUnder_prime w).pos
    have hle : ((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
      rw [Real.rpow_two]
      exact_mod_cast sq_rationalPrimeUnder_le_absNorm hw
    calc (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)
        ≤ (((rationalPrimeUnder w : ℕ) : ℝ) ^ (2 : ℝ)) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = ((rationalPrimeUnder w : ℕ) : ℝ) ^ (-(2 * s)) := by
          rw [← Real.rpow_mul hp.le]; ring_nf
  · rw [Set.indicator_of_notMem hw]
    positivity

/- English proof (translation)
The claim follows from `(summable_absNorm_rpow_neg hs).subtype S`.
-/
theorem summable_absNorm_rpow_neg_subtype (S : Set (HeightOneSpectrum (𝓞 L))) {s : ℝ}
    (hs : 1 < s) : Summable fun w : S => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_neg hs).subtype S

section relative

variable (K L) [Field K] [NumberField K] [Algebra K L]

def degreeOnePrimes : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | w.asIdeal.inertiaDeg (𝓞 K) = 1}

def higherDegreePrimes : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | 2 ≤ w.asIdeal.inertiaDeg (𝓞 K)}

/- English proof (translation)
Use extensionality with `w`. Use `Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)` as an intermediate fact. Simplify using `only [degreeOnePrimes, higherDegreePrimes, mem_compl_iff, mem_ofPred_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem compl_degreeOnePrimes : (degreeOnePrimes K L)ᶜ = higherDegreePrimes K L := by
  ext w
  have := Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)
  simp only [degreeOnePrimes, higherDegreePrimes, mem_compl_iff, mem_ofPred_eq]
  omega

variable {K L}

/- English proof (translation)
Rewrite using `[← Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under (𝓞 K)) w.asIdeal]`. Establish `: 2 ≤ w.asIdeal.inertiaDeg (𝓞 K)` using `hw`. Conclude with `Nat.Prime.not_prime_pow' (by omega)`.
-/
theorem not_prime_absNorm_of_mem_higherDegreePrimes {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ higherDegreePrimes K L) : ¬ (Ideal.absNorm w.asIdeal).Prime := by
  rw [← Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under (𝓞 K)) w.asIdeal]
  have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 K) := hw
  exact Nat.Prime.not_prime_pow' (by omega)

/- English proof (translation)
Introduce `_ hw` and use `not_prime_absNorm_of_mem_higherDegreePrimes hw`.
-/
theorem higherDegreePrimes_subset :
    higherDegreePrimes K L ⊆ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime} :=
  fun _ hw => not_prime_absNorm_of_mem_higherDegreePrimes hw

/- English proof (translation)
The claim follows from `(summable_subtype_iff_indicator (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}) (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp (summable_absNorm_rpow_neg_of_not_prime hs)`.
-/
theorem summable_indicator_not_prime {s : ℝ} (hs : 1 / 2 < s) :
    Summable ({w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
      fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)) :=
  (summable_subtype_iff_indicator
    (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime})
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp
    (summable_absNorm_rpow_neg_of_not_prime hs)

variable (K L) in

/- English proof (translation)
Use `(summable_subtype_iff_indicator (s := higherDegreePrimes K L) (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_` and prove the remaining obligations. Use `Summable.of_nonneg_of_le (fun w => indicator_nonneg (fun _ _ => by positivity) w) (fun w => ?_) (summable_indicator_not_prime hs)` and prove the remaining obligations. Conclude with `indicator_le_indicator_of_subset higherDegreePrimes_subset (fun _ => by positivity) w`.
-/
theorem summable_higherDegreePrimes {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : higherDegreePrimes K L => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by
  refine (summable_subtype_iff_indicator (s := higherDegreePrimes K L)
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_
  refine Summable.of_nonneg_of_le (fun w => indicator_nonneg (fun _ _ => by positivity) w)
    (fun w => ?_) (summable_indicator_not_prime hs)
  exact indicator_le_indicator_of_subset higherDegreePrimes_subset (fun _ => by positivity) w

variable (K L) in

/- English proof (translation)
Use `⟨∑' w, {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 : ℝ))) w, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h1` using `summable_indicator_not_prime (L := L) (s := 1) (by norm_num)`. Establish `hs'` using `(summable_subtype_iff_indicator (s := higherDegreePrimes K L) (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp (summable_higherDegreePrimes K L (by linarith))`. Rewrite using `[Set.primeIdealZetaSum_def, tsum_subtype (higherDegreePrimes K L) (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]`. Use `Summable.tsum_le_tsum (fun w => ?_) hs' h1` and prove the remaining obligations.

Distinguish the cases in `hw : w ∈ higherDegreePrimes K L`. Rewrite using `[indicator_of_mem hw, indicator_of_mem (higherDegreePrimes_subset hw)]`. Conclude with `Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_absNorm w) (by linarith)`. Rewrite using `[indicator_of_notMem hw]`. Conclude with `indicator_nonneg (fun _ _ => by positivity) w`.
-/
theorem primeIdealZetaSum_higherDegreePrimes_le :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → (higherDegreePrimes K L).primeIdealZetaSum s ≤ C := by
  refine ⟨∑' w, {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
    (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 : ℝ))) w,
    fun s hs => ?_⟩
  have h1 := summable_indicator_not_prime (L := L) (s := 1) (by norm_num)
  have hs' := (summable_subtype_iff_indicator (s := higherDegreePrimes K L)
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp
    (summable_higherDegreePrimes K L (by linarith))
  rw [Set.primeIdealZetaSum_def, tsum_subtype (higherDegreePrimes K L)
    (fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]
  refine Summable.tsum_le_tsum (fun w => ?_) hs' h1
  by_cases hw : w ∈ higherDegreePrimes K L
  · rw [indicator_of_mem hw, indicator_of_mem (higherDegreePrimes_subset hw)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_absNorm w) (by linarith)
  · rw [indicator_of_notMem hw]
    exact indicator_nonneg (fun _ _ => by positivity) w

variable (K L) in

/- English proof (translation)
Take `⟨C, hC⟩` from `primeIdealZetaSum_higherDegreePrimes_le K L`. Conclude with `isBoundedUnder_of_eventually_le (a := C) (eventually_nhdsWithin_of_forall fun s hs => hC s (le_of_lt hs))`.
-/
theorem isBoundedUnder_primeIdealZetaSum_higherDegreePrimes :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => (higherDegreePrimes K L).primeIdealZetaSum s := by
  obtain ⟨C, hC⟩ := primeIdealZetaSum_higherDegreePrimes_le K L
  exact isBoundedUnder_of_eventually_le (a := C)
    (eventually_nhdsWithin_of_forall fun s hs => hC s (le_of_lt hs))

end relative

end

end GroundTheory.Global
