import Mathlib
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.InvDiffLocal

open IsDedekindDomain.HeightOneSpectrum in

/- English proof (translation)
Take `⟨⟨a, ⟨b, hb⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors R) t`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Rewrite `ht` using `[valuation_of_mk']`. Use `set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn`. Establish `hvb : v.intValuation b = WithZero.exp (-(n : ℤ))` using `v.intValuation_if_neg hb0`.

Establish `hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b`. Rewrite using `[hvb]`. Conclude with `WithZero.exp_pos`. Establish `hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ))`. Rewrite using `[← hvb]`.

Conclude with `(div_le_one₀ hpos).1 ht`. Establish `haI : a ∈ v.asIdeal ^ n` using `(v.intValuation_le_pow_iff_mem a n).1 hva`. Establish `hbI : b ∈ v.asIdeal ^ n` using `(v.intValuation_le_pow_iff_mem b n).1 hvb.le`. Establish `hbI' : b ∉ v.asIdeal ^ (n + 1)`. Introduce `h`.

Use `(v.intValuation_le_pow_iff_mem b (n + 1)).2 h` as an intermediate fact. Rewrite `this` using `[hvb]`. Establish `h2` using `WithZero.exp_le_exp.1 this`. Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers.

Establish `hdvd : v.asIdeal ^ n ∣ Ideal.span {b}` using `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)`. Take `⟨B', hB'⟩` from `hdvd`. Establish `hB'p : ¬ B' ≤ v.asIdeal`. Introduce `hle`. Apply `hbI'` to reduce the goal to its premises.

Establish `: Ideal.span {b} ≤ v.asIdeal ^ (n + 1)`. Rewrite using `[hB', pow_succ]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self b)`. Take `⟨s, hsB, hsp⟩` from `Set.not_subset.1 hB'p`.

Use `⟨s, hsp, ?_⟩` and prove the remaining obligations. Establish `hmem : a * s ∈ Ideal.span {b}`. Rewrite using `[hB']`. Conclude with `Ideal.mul_mem_mul haI hsB`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Use `show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r`. Rewrite using `[IsFractionRing.mk'_eq_div]`. Establish `hbK : algebraMap R K b ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]`.

Conclude with `hb0`. Rewrite using `[mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]`.
-/
theorem exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [valuation_of_mk'] at ht
  set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn
  have hvb : v.intValuation b = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hb0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b := by
    rw [hvb]; exact WithZero.exp_pos
  have hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hvb]; exact (div_le_one₀ hpos).1 ht
  have haI : a ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem a n).1 hva
  have hbI : b ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem b n).1 hvb.le
  have hbI' : b ∉ v.asIdeal ^ (n + 1) := by
    intro h
    have := (v.intValuation_le_pow_iff_mem b (n + 1)).2 h
    rw [hvb] at this
    have h2 := WithZero.exp_le_exp.1 this
    push_cast at h2
    omega
  have hdvd : v.asIdeal ^ n ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)
  obtain ⟨B', hB'⟩ := hdvd
  have hB'p : ¬ B' ≤ v.asIdeal := by
    intro hle
    apply hbI'
    have : Ideal.span {b} ≤ v.asIdeal ^ (n + 1) := by
      rw [hB', pow_succ]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self b)
  obtain ⟨s, hsB, hsp⟩ := Set.not_subset.1 hB'p
  refine ⟨s, hsp, ?_⟩
  have hmem : a * s ∈ Ideal.span {b} := by
    rw [hB']; exact Ideal.mul_mem_mul haI hsB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨r, ?_⟩
  show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r
  rw [IsFractionRing.mk'_eq_div]
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]; exact hb0
  rw [mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

/- English proof (translation)
Introduce `d hd`. Establish `hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L)`. Rewrite using `[FractionalIdeal.mem_dual (by simp)]`. Introduce `a ha`. Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`.

Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Conclude with `hx b`. Establish `hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L)` using `(FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩`. Rewrite `hdd` using `[coeIdeal_differentIdeal (𝓞 K) K]`. Establish `hm` using `FractionalIdeal.mul_mem_mul hxd hdd`.

Rewrite `hm` using `[mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))]`. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 hm`. Conclude with `⟨c, hc⟩`.
-/
theorem mul_mem_of_trace_mem {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by
  intro d hd
  have hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx b
  have hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal (𝓞 K) K] at hdd
  have hm := FractionalIdeal.mul_mem_mul hxd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

open IsDedekindDomain.HeightOneSpectrum in

/- English proof (translation)
Use `set S : Set (HeightOneSpectrum (𝓞 L)) := {la' | la' ≠ la ∧ la'.asIdeal.under (𝓞 K) = p.asIdeal}`. Use `haveI := p.isMaximal`. Establish `hfin : S.Finite`. Use `((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L)).preimage (f := HeightOneSpectrum.asIdeal) ?_).subset ?_` and prove the remaining obligations. Introduce `a _ b _ h`.

Conclude with `HeightOneSpectrum.ext h`. Introduce `la' h`. Conclude with `⟨la'.isPrime, ⟨h.2.symm⟩⟩`. Use `haveI := la.isPrime`. Establish `hw : ∀ la' ∈ S, ∃ w : 𝓞 L, w ∈ la'.asIdeal ^ N ∧ w ∉ la.asIdeal`.

Introduce `la' h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : la'.asIdeal ^ N ≤ la.asIdeal` using `fun w hw => hc w hw`. Establish `h2` using `Ideal.IsPrime.le_of_pow_le h1`.

Conclude with `h.1 (HeightOneSpectrum.ext (la'.isMaximal.eq_of_le la.isPrime.ne_top h2))`. Use `choose! w hwN hwla using hw`. Use `⟨∏ la' ∈ hfin.toFinset, w la', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨i, hi, hmem⟩`.

Conclude with `hwla i (hfin.mem_toFinset.1 hi) hmem`. Introduce `la' h1 h2`. Establish `hS : la' ∈ hfin.toFinset` using `hfin.mem_toFinset.2 ⟨h1, h2⟩`. Rewrite using `[← Finset.mul_prod_erase _ _ hS]`. Conclude with `Ideal.mul_mem_right _ _ (hwN la' ⟨h1, h2⟩)`.
-/
theorem exists_approx_idempotent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    ∃ z : 𝓞 L, z ∉ la.asIdeal ∧ ∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la →
      la'.asIdeal.under (𝓞 K) = p.asIdeal → z ∈ la'.asIdeal ^ N := by
  set S : Set (HeightOneSpectrum (𝓞 L)) := {la' | la' ≠ la ∧ la'.asIdeal.under (𝓞 K) = p.asIdeal}
  haveI := p.isMaximal
  have hfin : S.Finite := by
    refine ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L)).preimage
      (f := HeightOneSpectrum.asIdeal) ?_).subset ?_
    · intro a _ b _ h; exact HeightOneSpectrum.ext h
    · intro la' h
      exact ⟨la'.isPrime, ⟨h.2.symm⟩⟩
  haveI := la.isPrime
  have hw : ∀ la' ∈ S, ∃ w : 𝓞 L, w ∈ la'.asIdeal ^ N ∧ w ∉ la.asIdeal := by
    intro la' h
    by_contra hc
    push_neg at hc
    have h1 : la'.asIdeal ^ N ≤ la.asIdeal := fun w hw => hc w hw
    have h2 := Ideal.IsPrime.le_of_pow_le h1
    exact h.1 (HeightOneSpectrum.ext (la'.isMaximal.eq_of_le la.isPrime.ne_top h2))
  choose! w hwN hwla using hw
  refine ⟨∏ la' ∈ hfin.toFinset, w la', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, hi, hmem⟩
    exact hwla i (hfin.mem_toFinset.1 hi) hmem
  · intro la' h1 h2
    have hS : la' ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨h1, h2⟩
    rw [← Finset.mul_prod_erase _ _ hS]
    exact Ideal.mul_mem_right _ _ (hwN la' ⟨h1, h2⟩)

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

open IsDedekindDomain.HeightOneSpectrum in

/- English proof (translation)
Introduce `K L _ _ _ _ _ la p hp y ⟨N, hN⟩ d hd`. Take `⟨z, hzla, hzN⟩` from `exists_approx_idempotent (K := K) la p N`. Use `set x : L := (z : L) * y with hxdef`. Establish `hx : ∀ b : 𝓞 L, p.valuation K (Algebra.trace K L ((b : L) * x)) ≤ 1`. Introduce `b`.

Establish `h` using `hN (b * z) (fun la' h1 h2 => Ideal.mul_mem_left _ _ (hzN la' h1 h2))`. Rewrite using `[hxdef, ← mul_assoc]`. Simplify using `using h`. Use `set bs := RingOfIntegers.basis L`. Establish `hloc : ∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∃ r : 𝓞 K, algebraMap (𝓞 K) K s * Algebra.trace K L ((bs i : L) * x) = algebraMap (𝓞 K) K r` using `fun i => exists_not_mem_mul_mem p _ (hx (bs i))`.

Use `choose s hsp r hr using hloc`. Use `set s0 : 𝓞 K := ∏ i, s i with hs0`. Use `haveI := p.isPrime`. Establish `hs0p : s0 ∉ p.asIdeal`. Rewrite using `[hs0, Ideal.IsPrime.prod_mem_iff]`.

Introduce and unpack `⟨i, _, hi⟩`. Conclude with `hsp i hi`. Establish `hgen : ∀ b : 𝓞 L, algebraMap (𝓞 K) K s0 * Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range`. Introduce `b`. Establish `hb : b ∈ Submodule.span ℤ (Set.range bs)` using `by rw [bs.span_eq]; trivial`.

Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨i, rfl⟩` from `hb`. Rewrite using `[hs0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap _ _ (s i)), mul_assoc, hr i, ← map_mul]`. Conclude with `⟨_, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add b c _ _ hb hc`. Establish `: ((b + c : 𝓞 L) : L) * x = (b : L) * x + (c : L) * x` using `by push_cast; ring`. Rewrite using `[this, map_add, mul_add]`. Conclude with `add_mem hb hc`.

Consider the case `smul n b _ hb`. Establish `: ((n • b : 𝓞 L) : L) * x = n • ((b : L) * x)`. Rewrite using `[← smul_mul_assoc]`. Use `congr 1`. Rewrite using `[this, map_zsmul, mul_smul_comm]`.

Conclude with `zsmul_mem hb n`. Use `set x' : L := algebraMap (𝓞 K) L s0 * x with hx'def`. Establish `htr : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x') ∈ (algebraMap (𝓞 K) K).range`. Introduce `b`. Establish `: (b : L) * x' = (algebraMap (𝓞 K) K s0) • ((b : L) * x)`.

Rewrite using `[Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hx'def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_smul, smul_eq_mul]`. Conclude with `hgen b`. Take `⟨c, hc⟩` from `mul_mem_of_trace_mem x' htr d hd`.

Establish `hcle : la.valuation L (c : L) ≤ 1` using `la.valuation_le_one c`. Establish `hs0la : la.valuation L (algebraMap (𝓞 K) L s0) = 1`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]`. Use `le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hs0p ?_)` and prove the remaining obligations. Rewrite `h` using `[la.valuation_lt_one_iff_mem]`.

Rewrite using `[← hp]`. Conclude with `h`. Establish `hzla' : la.valuation L (z : L) = 1`. Use `le_antisymm (la.valuation_le_one z) (not_lt.1 fun h => hzla ?_)` and prove the remaining obligations. Conclude with `(la.valuation_lt_one_iff_mem z).1 h`.

Establish `: (c : L) = (algebraMap (𝓞 K) L s0 * (z : L)) * (y * (d : L))`. Rewrite using `[hc, hx'def, hxdef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hcle` using `[this, map_mul, map_mul, hs0la, hzla', one_mul, one_mul]`. Conclude with `hcle`.
-/
theorem valuation_mul_different_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)),
    la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L,
      (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal →
        b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) →
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  intro K L _ _ _ _ _ la p hp y ⟨N, hN⟩ d hd
  obtain ⟨z, hzla, hzN⟩ := exists_approx_idempotent (K := K) la p N
  set x : L := (z : L) * y with hxdef
  have hx : ∀ b : 𝓞 L, p.valuation K (Algebra.trace K L ((b : L) * x)) ≤ 1 := by
    intro b
    have h := hN (b * z) (fun la' h1 h2 => Ideal.mul_mem_left _ _ (hzN la' h1 h2))
    rw [hxdef, ← mul_assoc]
    simpa using h
  set bs := RingOfIntegers.basis L
  have hloc : ∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K s * Algebra.trace K L ((bs i : L) * x) = algebraMap (𝓞 K) K r :=
    fun i => exists_not_mem_mul_mem p _ (hx (bs i))
  choose s hsp r hr using hloc
  set s0 : 𝓞 K := ∏ i, s i with hs0
  haveI := p.isPrime
  have hs0p : s0 ∉ p.asIdeal := by
    rw [hs0, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, _, hi⟩
    exact hsp i hi
  have hgen : ∀ b : 𝓞 L,
      algebraMap (𝓞 K) K s0 * Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have hb : b ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      rw [hs0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap _ _ (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      have : ((b + c : 𝓞 L) : L) * x = (b : L) * x + (c : L) * x := by push_cast; ring
      rw [this, map_add, mul_add]
      exact add_mem hb hc
    | smul n b _ hb =>
      have : ((n • b : 𝓞 L) : L) * x = n • ((b : L) * x) := by
        rw [← smul_mul_assoc]; congr 1
      rw [this, map_zsmul, mul_smul_comm]
      exact zsmul_mem hb n
  set x' : L := algebraMap (𝓞 K) L s0 * x with hx'def
  have htr : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x') ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have : (b : L) * x' = (algebraMap (𝓞 K) K s0) • ((b : L) * x) := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hx'def]; ring
    rw [this, map_smul, smul_eq_mul]
    exact hgen b
  obtain ⟨c, hc⟩ := mul_mem_of_trace_mem x' htr d hd
  have hcle : la.valuation L (c : L) ≤ 1 := la.valuation_le_one c
  have hs0la : la.valuation L (algebraMap (𝓞 K) L s0) = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hs0p ?_)
    rw [la.valuation_lt_one_iff_mem] at h
    rw [← hp]
    exact h
  have hzla' : la.valuation L (z : L) = 1 := by
    refine le_antisymm (la.valuation_le_one z) (not_lt.1 fun h => hzla ?_)
    exact (la.valuation_lt_one_iff_mem z).1 h
  have : (c : L) = (algebraMap (𝓞 K) L s0 * (z : L)) * (y * (d : L)) := by
    rw [hc, hx'def, hxdef]; ring
  rw [this, map_mul, map_mul, hs0la, hzla', one_mul, one_mul] at hcle
  exact hcle

end GlobalTheory.InvDiffLocal
