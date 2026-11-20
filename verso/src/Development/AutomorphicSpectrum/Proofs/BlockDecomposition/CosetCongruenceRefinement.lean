import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi.CosetStep

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `hv : v.asIdeal ≠ ⊤` using `v.isPrime.ne_top`. Establish `hex : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hD` to reduce the goal to its premises.

Establish `h' : D ≤ ⨅ i : ℕ, v.asIdeal ^ i`. Use `le_iInf fun i => ?_` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `zero => simp`. Consider the case `succ i => exact h i`.

Rewrite `h'` using `[Ideal.iInf_pow_eq_bot_of_isDomain _ hv]`. Conclude with `le_bot_iff.mp h'`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hle⟩ : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) ∧ D ≤ v.asIdeal ^ m := by`. Use `⟨Nat.find hex, Nat.find_spec hex, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos` into its components or cases.

Simplify using `[h0]`. Establish `h1` using `Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos) push_neg at h1`. Establish `e : Nat.find hex - 1 + 1 = Nat.find hex` using `by omega`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Take `⟨B, hB⟩` from `Ideal.dvd_iff_le.mpr hle`.

Use `⟨m, B, hB, fun hBv => hm ?_⟩` and prove the remaining obligations. Rewrite using `[hB, pow_succ]`. Conclude with `Ideal.mul_mono_right hBv`.
-/
theorem exists_pow_mul (v : HeightOneSpectrum (𝓞 F)) {D : Ideal (𝓞 F)} (hD : D ≠ ⊥) :
    ∃ (m : ℕ) (B : Ideal (𝓞 F)), D = v.asIdeal ^ m * B ∧ ¬ B ≤ v.asIdeal := by
  have hv : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hex : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) := by
    by_contra h
    push_neg at h
    apply hD
    have h' : D ≤ ⨅ i : ℕ, v.asIdeal ^ i := by
      refine le_iInf fun i => ?_
      cases i with
      | zero => simp
      | succ i => exact h i
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hv] at h'
    exact le_bot_iff.mp h'
  obtain ⟨m, hm, hle⟩ : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) ∧ D ≤ v.asIdeal ^ m := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · simp [h0]
    · have h1 := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      push_neg at h1
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rwa [e] at h1
  obtain ⟨B, hB⟩ := Ideal.dvd_iff_le.mpr hle
  refine ⟨m, B, hB, fun hBv => hm ?_⟩
  rw [hB, pow_succ]
  exact Ideal.mul_mono_right hBv

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hle : v.asIdeal ^ k ≤ w.asIdeal` using `fun e he => h e he`. Establish `hvw : v.asIdeal ≤ w.asIdeal` using `w.isPrime.le_of_pow_le hle`. Conclude with `hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hvw).symm)`.
-/
theorem exists_mem_pow_not_mem {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ) :
    ∃ e ∈ v.asIdeal ^ k, e ∉ w.asIdeal := by
  by_contra h
  push_neg at h
  have hle : v.asIdeal ^ k ≤ w.asIdeal := fun e he => h e he
  have hvw : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hvw).symm)

/- English proof (translation)
Take `⟨s, hs, y, hy, hsy⟩` from `ha`. Take `⟨t, ht, z, hz, htz⟩` from `hb`. Use `⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * y + s * z, I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_left _ hz), ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(t : F) * hsy + (s : F) * htz`.
-/
theorem locMem_add {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a + b) := by
  obtain ⟨s, hs, y, hy, hsy⟩ := ha
  obtain ⟨t, ht, z, hz, htz⟩ := hb
  refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * y + s * z,
    I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_left _ hz), ?_⟩
  push_cast
  linear_combination (t : F) * hsy + (s : F) * htz

/- English proof (translation)
Take `⟨s, hs, y, hy, hsy⟩` from `ha`. Use `⟨s, hs, -y, I.neg_mem hy, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_neg, hsy]`.
-/
theorem locMem_neg {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a : F}
    (ha : LocMem I w a) : LocMem I w (-a) := by
  obtain ⟨s, hs, y, hy, hsy⟩ := ha
  refine ⟨s, hs, -y, I.neg_mem hy, ?_⟩
  push_cast
  rw [mul_neg, hsy]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `locMem_add ha (locMem_neg hb)`.
-/
theorem locMem_sub {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a - b) := by
  rw [sub_eq_add_neg]; exact locMem_add ha (locMem_neg hb)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, y, hy, h⟩`. Conclude with `⟨s, hs, y, (Ideal.mul_le_left : I * v.asIdeal ^ k ≤ I) hy, h⟩`. Introduce and unpack `⟨s, hs, y, hy, h⟩`. Take `⟨e, he, hew⟩` from `exists_mem_pow_not_mem hw k`.

Use `⟨e * s, fun hm => (w.isPrime.mem_or_mem hm).elim hew hs, y * e, Ideal.mul_mem_mul hy he, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_assoc, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locMem_mul_pow_iff {I : Ideal (𝓞 F)} {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ)
    {t : F} : LocMem (I * v.asIdeal ^ k) w t ↔ LocMem I w t := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    exact ⟨s, hs, y, (Ideal.mul_le_left : I * v.asIdeal ^ k ≤ I) hy, h⟩
  · rintro ⟨s, hs, y, hy, h⟩
    obtain ⟨e, he, hew⟩ := exists_mem_pow_not_mem hw k
    refine ⟨e * s, fun hm => (w.isPrime.mem_or_mem hm).elim hew hs, y * e, Ideal.mul_mem_mul hy he, ?_⟩
    push_cast
    rw [mul_assoc, h]
    ring

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(v.intValuation_le_pow_iff_mem y k).2 hy`.
-/
theorem val_le_of_mem_pow (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : y ∈ v.asIdeal ^ k) :
    v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem y k).2 hy

/- English proof (translation)
Rewrite `hy` using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(v.intValuation_le_pow_iff_mem y k).1 hy`.
-/
theorem mem_pow_of_val_le (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ))) :
    y ∈ v.asIdeal ^ k := by
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hy
  exact (v.intValuation_le_pow_iff_mem y k).1 hy

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs`.
-/
theorem val_eq_one_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : 𝓞 F} (hs : s ∉ v.asIdeal) :
    v.valuation F (algebraMap (𝓞 F) F s) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs

/- English proof (translation)
Use `show Valued.v (algebraMap F (Fv F v) t) ≤ _ ↔ _`. Rewrite using `[show Valued.v (algebraMap F (Fv F v) t) = v.valuation F t by first`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t`. Consider the case `rfl]`.
-/
theorem mem_ballV_iff (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (t : F) :
    algebraMap F (Fv F v) t ∈ ballV v k ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by
  show Valued.v (algebraMap F (Fv F v) t) ≤ _ ↔ _
  rw [show Valued.v (algebraMap F (Fv F v) t) = v.valuation F t by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t
      | rfl]

/- English proof (translation)
Use `show Valued.v (a + b) ≤ _`. Conclude with `(Valuation.map_add _ a b).trans (max_le ha hb)`.
-/
theorem ballV_add {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {a b : Fv F v}
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a + b ∈ ballV v k := by
  show Valued.v (a + b) ≤ _
  exact (Valuation.map_add _ a b).trans (max_le ha hb)

/- English proof (translation)
Use `show Valued.v (a - b) ≤ _`. Conclude with `(Valuation.map_sub _ a b).trans (max_le ha hb)`.
-/
theorem ballV_sub {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {a b : Fv F v}
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a - b ∈ ballV v k := by
  show Valued.v (a - b) ≤ _
  exact (Valuation.map_sub _ a b).trans (max_le ha hb)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, y, hy, h⟩`. Establish `h1` using `val_le_of_mem_pow v ((Ideal.mul_le_right : I * v.asIdeal ^ k ≤ v.asIdeal ^ k) hy)`. Establish `h2` using `val_eq_one_of_not_mem v hs`. Establish `h3 : v.valuation F (algebraMap (𝓞 F) F s * t) = v.valuation F (algebraMap (𝓞 F) F y)`.

Conclude with `congrArg (v.valuation F) h`. Rewrite `h3` using `[map_mul, h2, one_mul]`. Rewrite using `[h3]`. Conclude with `h1`. Introduce `ht`.

Take `⟨s0, hs0I, hs0v⟩` from `SetLike.not_le_iff_exists.mp hI`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) t`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbF : algebraMap (𝓞 F) F b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Establish `hspan : Ideal.span {b} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Take `⟨m, B, hbB, hBv⟩` from `exists_pow_mul v hspan`. Take `⟨c, hcB, hcv⟩` from `SetLike.not_le_iff_exists.mp hBv`. Establish `hbm : b ∈ v.asIdeal ^ m`. Establish `hb' : b ∈ Ideal.span {b}` using `Ideal.subset_span rfl`.

Rewrite `hb'` using `[hbB]`. Conclude with `(Ideal.mul_le_left : v.asIdeal ^ m * B ≤ v.asIdeal ^ m) hb'`. Establish `hk1 : WithZero.exp (-(k : ℤ)) ≤ 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `hvala : v.valuation F (algebraMap (𝓞 F) F a) ≤ WithZero.exp (-(m : ℤ))`. Establish `e : algebraMap (𝓞 F) F a = (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) * algebraMap (𝓞 F) F b`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `ham : a ∈ v.asIdeal ^ m` using `mem_pow_of_val_le v hvala`. Establish `hac : a * c ∈ Ideal.span {b}`. Rewrite using `[hbB]`. Conclude with `Ideal.mul_mem_mul ham hcB`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hac`.

Establish `hrF : algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F r`. Use `congrArg (algebraMap (𝓞 F) F) hr` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-this`.

Establish `hvr : v.valuation F (algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(k : ℤ))`. Rewrite using `[← hrF, map_mul, val_eq_one_of_not_mem v hcv, one_mul]`. Conclude with `ht`. Establish `hrk : r ∈ v.asIdeal ^ k` using `mem_pow_of_val_le v hvr`. Use `⟨s0 * c, fun hm => (v.isPrime.mem_or_mem hm).elim hs0v hcv, s0 * r, Ideal.mul_mem_mul hs0I hrk, ?_⟩` and prove the remaining obligations.

Establish `e1 : ((s0 * c : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F c`. Rewrite using `[← map_mul]`. Establish `e2 : ((s0 * r : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F r`. Rewrite using `[← map_mul]`. Rewrite using `[e1, e2, ← hrF]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem locMem_v_iff {I : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hI : ¬ I ≤ v.asIdeal) (k : ℕ)
    (t : F) : LocMem (I * v.asIdeal ^ k) v t ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    have h1 := val_le_of_mem_pow v ((Ideal.mul_le_right : I * v.asIdeal ^ k ≤ v.asIdeal ^ k) hy)
    have h2 := val_eq_one_of_not_mem v hs
    have h3 : v.valuation F (algebraMap (𝓞 F) F s * t) = v.valuation F (algebraMap (𝓞 F) F y) := by
      exact congrArg (v.valuation F) h
    rw [map_mul, h2, one_mul] at h3
    rw [h3]
    exact h1
  · intro ht
    obtain ⟨s0, hs0I, hs0v⟩ := SetLike.not_le_iff_exists.mp hI
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) t
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap (𝓞 F) F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hspan : Ideal.span {b} ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨m, B, hbB, hBv⟩ := exists_pow_mul v hspan
    obtain ⟨c, hcB, hcv⟩ := SetLike.not_le_iff_exists.mp hBv
    have hbm : b ∈ v.asIdeal ^ m := by
      have hb' : b ∈ Ideal.span {b} := Ideal.subset_span rfl
      rw [hbB] at hb'
      exact (Ideal.mul_le_left : v.asIdeal ^ m * B ≤ v.asIdeal ^ m) hb'
    have hk1 : WithZero.exp (-(k : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hvala : v.valuation F (algebraMap (𝓞 F) F a) ≤ WithZero.exp (-(m : ℤ)) := by
      have e : algebraMap (𝓞 F) F a =
          (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) * algebraMap (𝓞 F) F b := by
        field_simp
      rw [e, map_mul]
      calc _ ≤ 1 * WithZero.exp (-(m : ℤ)) := mul_le_mul' (ht.trans hk1) (val_le_of_mem_pow v hbm)
        _ = _ := one_mul _
    have ham : a ∈ v.asIdeal ^ m := mem_pow_of_val_le v hvala
    have hac : a * c ∈ Ideal.span {b} := by
      rw [hbB]
      exact Ideal.mul_mem_mul ham hcB
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hac
    have hrF : algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) =
        algebraMap (𝓞 F) F r := by
      have := congrArg (algebraMap (𝓞 F) F) hr
      rw [map_mul, map_mul] at this
      field_simp
      linear_combination -this
    have hvr : v.valuation F (algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(k : ℤ)) := by
      rw [← hrF, map_mul, val_eq_one_of_not_mem v hcv, one_mul]
      exact ht
    have hrk : r ∈ v.asIdeal ^ k := mem_pow_of_val_le v hvr
    refine ⟨s0 * c, fun hm => (v.isPrime.mem_or_mem hm).elim hs0v hcv, s0 * r,
      Ideal.mul_mem_mul hs0I hrk, ?_⟩
    have e1 : ((s0 * c : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F c := by
      rw [← map_mul]
    have e2 : ((s0 * r : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F r := by
      rw [← map_mul]
    rw [e1, e2, ← hrF]
    ring

/- English proof (translation)
Establish `hd : DenseRange (algebraMap F (Fv F v))` using `HeightOneSpectrum.denseRange_algebraMap F v`. Establish `hval : ∀ t : F, Valued.v (algebraMap F (Fv F v) t) = v.valuation F t` using `fun t => by first`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t`. Consider the case `rfl`.

Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer (K := F) v`. Establish `hvp : Valued.v (algebraMap F (Fv F v) (π ^ k)) = WithZero.exp (-(k : ℤ))`. Rewrite using `[hval, map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]`. Establish `hp0 : algebraMap F (Fv F v) (π ^ k) ≠ 0`. Introduce `h`.

Rewrite `hvp` using `[h, map_zero]`. Conclude with `absurd hvp.symm (by simp)`. Establish `hopen : IsOpen {z : Fv F v | Valued.v z ≤ WithZero.exp (-(k : ℤ))}`. Establish `h1` using `Valued.isOpen_closedBall (R := Fv F v) (r := (Valued.v : Valuation (Fv F v) _).restrict (algebraMap F (Fv F v) (π ^ k))) ((Valuation.ne_zero_iff _).mpr hp0)`. Use `h1 using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Rewrite using `[Valuation.restrict_le_iff, hvp]`. Establish `ho : IsOpen {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))}` using `hopen.preimage (continuous_id.sub continuous_const)`. Establish `hmem : {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} ∈ 𝓝 c` using `ho.mem_nhds (by simp)`. Take `⟨a, ha⟩` from `hd.mem_nhds hmem`.

Conclude with `⟨a, ha⟩`.
-/
theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c : Fv F v) :
    ∃ a : F, algebraMap F (Fv F v) a - c ∈ ballV v k := by
  have hd : DenseRange (algebraMap F (Fv F v)) := HeightOneSpectrum.denseRange_algebraMap F v
  have hval : ∀ t : F, Valued.v (algebraMap F (Fv F v) t) = v.valuation F t := fun t => by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t
      | rfl
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := F) v
  have hvp : Valued.v (algebraMap F (Fv F v) (π ^ k)) = WithZero.exp (-(k : ℤ)) := by
    rw [hval, map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have hp0 : algebraMap F (Fv F v) (π ^ k) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvp
    exact absurd hvp.symm (by simp)
  have hopen : IsOpen {z : Fv F v | Valued.v z ≤ WithZero.exp (-(k : ℤ))} := by
    have h1 := Valued.isOpen_closedBall (R := Fv F v)
      (r := (Valued.v : Valuation (Fv F v) _).restrict (algebraMap F (Fv F v) (π ^ k)))
      ((Valuation.ne_zero_iff _).mpr hp0)
    convert h1 using 2
    funext z
    rw [Valuation.restrict_le_iff, hvp]
  have ho : IsOpen {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hmem : {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} ∈ 𝓝 c :=
    ho.mem_nhds (by simp)
  obtain ⟨a, ha⟩ := hd.mem_nhds hmem
  exact ⟨a, ha⟩

/- English proof (translation)
Establish `hcop : C ⊔ v.asIdeal ^ M = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ h`. Establish `h1 : v.asIdeal ^ M ≤ P` using `le_sup_right.trans hle`. Establish `h2 : C ≤ P` using `le_sup_left.trans hle`.

Establish `h3 : v.asIdeal ≤ P` using `hP.isPrime.le_of_pow_le h1`. Establish `h4 : v.asIdeal = P` using `v.isMaximal.eq_of_le hP.ne_top h3`. Conclude with `hC (h4 ▸ h2)`. Establish `h1 : (1 : 𝓞 F) ∈ C ⊔ v.asIdeal ^ M` using `hcop ▸ Submodule.mem_top`. Take `⟨e, he, f, hf, hef⟩` from `Submodule.mem_sup.mp h1`.

Conclude with `⟨e, he, f, hf, hef⟩`.
-/
private theorem exists_add_eq_one_lemma {v : HeightOneSpectrum (𝓞 F)} {C : Ideal (𝓞 F)}
    (hC : ¬ C ≤ v.asIdeal) (M : ℕ) : ∃ e ∈ C, ∃ f ∈ v.asIdeal ^ M, e + f = 1 := by
  have hcop : C ⊔ v.asIdeal ^ M = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    have h1 : v.asIdeal ^ M ≤ P := le_sup_right.trans hle
    have h2 : C ≤ P := le_sup_left.trans hle
    have h3 : v.asIdeal ≤ P := hP.isPrime.le_of_pow_le h1
    have h4 : v.asIdeal = P := v.isMaximal.eq_of_le hP.ne_top h3
    exact hC (h4 ▸ h2)
  have h1 : (1 : 𝓞 F) ∈ C ⊔ v.asIdeal ^ M := hcop ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  exact ⟨e, he, f, hf, hef⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_near v k c`. Take `⟨a', b', hb', hab⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) (a - x0)`. Establish `hb0 : b' ≠ 0` using `nonZeroDivisors.ne_zero hb'`. Establish `hbF : algebraMap (𝓞 F) F b' ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'`. Establish `hspan : Ideal.span {b'} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Take `⟨r, B', hbB, hB'v⟩` from `exists_pow_mul v hspan`. Take `⟨m, B, hIB, hBv⟩` from `exists_pow_mul v hI`. Establish `hCv : ¬ B' * B ≤ v.asIdeal` using `fun hle => (v.isPrime.mul_le.mp hle).elim hB'v hBv`. Take `⟨e, he, f, hf, hef⟩` from `exists_add_eq_one_lemma hCv (k + r)`.

Take `⟨g, hgB', hgv⟩` from `SetLike.not_le_iff_exists.mp hB'v`. Establish `hgF : algebraMap (𝓞 F) F g ≠ 0`. Introduce `h0`. Apply `hgv` to reduce the goal to its premises. Rewrite using `[(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp h0]`.

Conclude with `v.asIdeal.zero_mem`. Establish `hfg : f * g ∈ Ideal.span {b'} * v.asIdeal ^ k`. Establish `e1 : v.asIdeal ^ (k + r) * B' = Ideal.span {b'} * v.asIdeal ^ k`. Rewrite using `[hbB, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← e1]`. Conclude with `Ideal.mul_mem_mul hf hgB'`. Take `⟨h, hh, hbh⟩` from `Ideal.mem_span_singleton_mul.mp hfg`. Use `⟨x0 + (a - x0) * algebraMap (𝓞 F) F e, fun w hw => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_cancel_left]`.

Take `⟨s1, hs1, hs1w⟩` from `exists_mem_pow_not_mem hw r`. Take `⟨s2, hs2, hs2w⟩` from `exists_mem_pow_not_mem hw m`. Establish `hs1e : s1 * e ∈ Ideal.span {b'} * B`. Establish `e2 : v.asIdeal ^ r * (B' * B) = Ideal.span {b'} * B`. Rewrite using `[hbB]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e2]`. Conclude with `Ideal.mul_mem_mul hs1 he`. Take `⟨β, hβ, hbβ⟩` from `Ideal.mem_span_singleton_mul.mp hs1e`. Use `⟨s2 * s1, fun hm => (w.isPrime.mem_or_mem hm).elim hs2w hs1w, s2 * (a' * β), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hIB]`. Conclude with `Ideal.mul_mem_mul hs2 (B.mul_mem_left _ hβ)`. Establish `h1` using `congrArg (algebraMap (𝓞 F) F) hbβ`. Rewrite `h1` using `[map_mul, map_mul]`. Establish `e1 : ((s2 * s1 : 𝓞 F) : F) = algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F s1`.

Rewrite using `[← map_mul]`. Establish `e2 : ((s2 * (a' * β) : 𝓞 F) : F) = algebraMap (𝓞 F) F s2 * (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F β)`. Rewrite using `[← map_mul, ← map_mul]`. Rewrite using `[e1, e2, ← hab]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(-(algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F a')) * h1`. Establish `hy : algebraMap F (Fv F v) (x0 + (a - x0) * algebraMap (𝓞 F) F e) - c = algebraMap F (Fv F v) ((a - x0) * algebraMap (𝓞 F) F e - (a - x0)) + (algebraMap F (Fv F v) a - c)`. Rewrite using `[map_sub, map_add, map_mul, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy]`.

Use `ballV_add ((mem_ballV_iff v k _).mpr ?_) ha` and prove the remaining obligations. Establish `e3 : (a - x0) * algebraMap (𝓞 F) F e - (a - x0) = -(algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F h / algebraMap (𝓞 F) F g)`. Establish `h1` using `congrArg (algebraMap (𝓞 F) F) hbh`. Establish `h2` using `congrArg (algebraMap (𝓞 F) F) hef`. Rewrite `h1` using `[map_mul, map_mul]`.

Rewrite `h2` using `[map_add, map_one]`. Rewrite using `[← hab]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F g) * h2 + algebraMap (𝓞 F) F a' * h1`. Rewrite using `[e3, Valuation.map_neg, map_div₀, map_mul, val_eq_one_of_not_mem v hgv, div_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_approx {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (x0 : F) (c : Fv F v) :
    ∃ x1 : F, (∀ w, w ≠ v → LocMem I w (x1 - x0)) ∧ algebraMap F (Fv F v) x1 - c ∈ ballV v k := by
  obtain ⟨a, ha⟩ := exists_near v k c
  obtain ⟨a', b', hb', hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (a - x0)
  have hb0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hbF : algebraMap (𝓞 F) F b' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
  have hspan : Ideal.span {b'} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨r, B', hbB, hB'v⟩ := exists_pow_mul v hspan
  obtain ⟨m, B, hIB, hBv⟩ := exists_pow_mul v hI
  have hCv : ¬ B' * B ≤ v.asIdeal := fun hle => (v.isPrime.mul_le.mp hle).elim hB'v hBv
  obtain ⟨e, he, f, hf, hef⟩ := exists_add_eq_one_lemma hCv (k + r)
  obtain ⟨g, hgB', hgv⟩ := SetLike.not_le_iff_exists.mp hB'v
  have hgF : algebraMap (𝓞 F) F g ≠ 0 := by
    intro h0
    apply hgv
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp h0]
    exact v.asIdeal.zero_mem
  have hfg : f * g ∈ Ideal.span {b'} * v.asIdeal ^ k := by
    have e1 : v.asIdeal ^ (k + r) * B' = Ideal.span {b'} * v.asIdeal ^ k := by
      rw [hbB, pow_add]
      ring
    rw [← e1]
    exact Ideal.mul_mem_mul hf hgB'
  obtain ⟨h, hh, hbh⟩ := Ideal.mem_span_singleton_mul.mp hfg
  refine ⟨x0 + (a - x0) * algebraMap (𝓞 F) F e, fun w hw => ?_, ?_⟩
  · rw [add_sub_cancel_left]
    obtain ⟨s1, hs1, hs1w⟩ := exists_mem_pow_not_mem hw r
    obtain ⟨s2, hs2, hs2w⟩ := exists_mem_pow_not_mem hw m
    have hs1e : s1 * e ∈ Ideal.span {b'} * B := by
      have e2 : v.asIdeal ^ r * (B' * B) = Ideal.span {b'} * B := by
        rw [hbB]
        ring
      rw [← e2]
      exact Ideal.mul_mem_mul hs1 he
    obtain ⟨β, hβ, hbβ⟩ := Ideal.mem_span_singleton_mul.mp hs1e
    refine ⟨s2 * s1, fun hm => (w.isPrime.mem_or_mem hm).elim hs2w hs1w, s2 * (a' * β), ?_, ?_⟩
    · rw [hIB]
      exact Ideal.mul_mem_mul hs2 (B.mul_mem_left _ hβ)
    · have h1 := congrArg (algebraMap (𝓞 F) F) hbβ
      rw [map_mul, map_mul] at h1
      have e1 : ((s2 * s1 : 𝓞 F) : F) = algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F s1 := by
        rw [← map_mul]
      have e2 : ((s2 * (a' * β) : 𝓞 F) : F) =
          algebraMap (𝓞 F) F s2 * (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F β) := by
        rw [← map_mul, ← map_mul]
      rw [e1, e2, ← hab]
      field_simp
      linear_combination (-(algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F a')) * h1
  · have hy : algebraMap F (Fv F v) (x0 + (a - x0) * algebraMap (𝓞 F) F e) - c =
        algebraMap F (Fv F v) ((a - x0) * algebraMap (𝓞 F) F e - (a - x0)) +
          (algebraMap F (Fv F v) a - c) := by
      rw [map_sub, map_add, map_mul, map_sub]
      ring
    rw [hy]
    refine ballV_add ((mem_ballV_iff v k _).mpr ?_) ha
    have e3 : (a - x0) * algebraMap (𝓞 F) F e - (a - x0) =
        -(algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F h / algebraMap (𝓞 F) F g) := by
      have h1 := congrArg (algebraMap (𝓞 F) F) hbh
      have h2 := congrArg (algebraMap (𝓞 F) F) hef
      rw [map_mul, map_mul] at h1
      rw [map_add, map_one] at h2
      rw [← hab]
      field_simp
      linear_combination (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F g) * h2 +
        algebraMap (𝓞 F) F a' * h1
    rw [e3, Valuation.map_neg, map_div₀, map_mul, val_eq_one_of_not_mem v hgv, div_one]
    calc _ ≤ 1 * WithZero.exp (-(k : ℤ)) :=
          mul_le_mul' (HeightOneSpectrum.valuation_le_one v a') (val_le_of_mem_pow v hh)
      _ = _ := one_mul _

/- English proof (translation)
Introduce `F _ _ ι S v hvS I hI hIv k x0 c`. Use `choose x1 hx1w hx1v using fun i => exists_approx hI v k (x0 i) (c i)`. Use `⟨x1, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [cosetOff, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, hball⟩ w hwS i`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[locMem_v_iff hIv, ← mem_ballV_iff, map_sub]`. Establish `h3` using `ballV_sub (hball i) (hx1v i)`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `h1 : LocMem I w (x i - x0 i)` using `hx w (by simp [hwv, hwS]) i`. Establish `h2` using `locMem_sub h1 (hx1w i w hwv)`. Rewrite using `[locMem_mul_pow_iff hwv]`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `hx`. Use `⟨fun w hw i => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hwv : w ≠ v` using `fun h => hw (by simp [h])`.

Establish `hwS : w ∉ S` using `fun h => hw (by simp [h])`. Establish `h1` using `(locMem_mul_pow_iff hwv k).mp (hx w hwS i)`. Establish `h2` using `locMem_add h1 (hx1w i w hwv)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `(locMem_v_iff hIv k (x i - x1 i)).mp (hx v hvS i)`. Rewrite `h1` using `[← mem_ballV_iff, map_sub]`. Establish `h3` using `ballV_add h1 (hx1v i)`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem coset_step : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  intro F _ _ ι S v hvS I hI hIv k x0 c
  choose x1 hx1w hx1v using fun i => exists_approx hI v k (x0 i) (c i)
  refine ⟨x1, fun x => ?_⟩
  simp only [cosetOff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hball⟩ w hwS i
    by_cases hwv : w = v
    · subst hwv
      rw [locMem_v_iff hIv, ← mem_ballV_iff, map_sub]
      have h3 := ballV_sub (hball i) (hx1v i)
      convert h3 using 1
      abel
    · have h1 : LocMem I w (x i - x0 i) := hx w (by simp [hwv, hwS]) i
      have h2 := locMem_sub h1 (hx1w i w hwv)
      rw [locMem_mul_pow_iff hwv]
      convert h2 using 1
      ring
  · intro hx
    refine ⟨fun w hw i => ?_, fun i => ?_⟩
    · have hwv : w ≠ v := fun h => hw (by simp [h])
      have hwS : w ∉ S := fun h => hw (by simp [h])
      have h1 := (locMem_mul_pow_iff hwv k).mp (hx w hwS i)
      have h2 := locMem_add h1 (hx1w i w hwv)
      convert h2 using 1
      ring
    · have h1 := (locMem_v_iff hIv k (x i - x1 i)).mp (hx v hvS i)
      rw [← mem_ballV_iff, map_sub] at h1
      have h3 := ballV_add h1 (hx1v i)
      convert h3 using 1
      abel

end GlobalTheory.CompanionTheory.Equi.CosetStep

end
