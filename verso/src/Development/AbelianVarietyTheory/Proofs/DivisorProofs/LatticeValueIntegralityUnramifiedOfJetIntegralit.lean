import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddiStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatValUnr

section Sz

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

/- English proof (translation)
Take `⟨hx, hx'⟩` from `hx`. Take `⟨hy, hy'⟩` from `hy`. Use `⟨mul_mem hx hy, ?_⟩` and prove the remaining obligations. Establish `: (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩` using `rfl`. Rewrite using `[this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]`.

Conclude with `mul_le_mul hx' hy' (norm_nonneg _) (by positivity)`.
-/
theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

/- English proof (translation)
Take `⟨hx, hx'⟩` from `hx`. Conclude with `⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩`.
-/
theorem sz_mono {r r' : ℝ} {x : ℂ} (hx : Sz l lam r x) (h : r ≤ r') : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))`.
-/
theorem norm_nat_le (n : ℕ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

/- English proof (translation)
Use `⟨natCast_mem _ n, ?_⟩` and prove the remaining obligations. Establish `: (⟨(n : ℂ), natCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ)` using `rfl`. Rewrite using `[this, map_natCast, Real.rpow_zero]`. Conclude with `norm_nat_le n`.
-/
theorem sz_nat (n : ℕ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨natCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), natCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := rfl
  rw [this, map_natCast, Real.rpow_zero]
  exact norm_nat_le n

/- English proof (translation)
Simplify using `using sz_nat (l := l) (lam := lam) 1`.
-/
theorem sz_one : Sz l lam 0 1 := by simpa using sz_nat (l := l) (lam := lam) 1

/- English proof (translation)
Take `⟨hx, hx'⟩` from `hx`. Use `⟨neg_mem hx, ?_⟩` and prove the remaining obligations. Establish `: (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩` using `rfl`. Rewrite using `[this, map_neg, norm_neg]` and apply the resulting hypothesis.
-/
theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

/- English proof (translation)
Break down `neg_one_pow_eq_or ℂ n with h | h` into its components or cases. Rewrite using `[h, one_mul]` and apply the resulting hypothesis. Rewrite using `[h, neg_one_mul]`. Conclude with `sz_neg hx`.
-/
theorem sz_neg_one_pow_mul {r : ℝ} {x : ℂ} (n : ℕ) (hx : Sz l lam r x) : Sz l lam r ((-1) ^ n * x) := by
  rcases neg_one_pow_eq_or ℂ n with h | h
  · rwa [h, one_mul]
  · rw [h, neg_one_mul]; exact sz_neg hx

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using sz_one (l := l) (lam := lam)`. Consider the case `succ n ih`. Use `sz_mul ih hx` as an intermediate fact. Rewrite using `[pow_succ]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam (n * r) (x ^ n) := by
  induction n with
  | zero => simpa using sz_one (l := l) (lam := lam)
  | succ n ih =>
    have := sz_mul ih hx
    rw [pow_succ]
    convert this using 1
    push_cast; ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using sz_one (l := l) (lam := lam)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `sz_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (x : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (x i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz_one (l := l) (lam := lam)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact sz_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Sz

/- English proof (translation)
Introduce `h`. Establish `h1` using `h.map (Algebra.norm ℤ : 𝓞 E →* ℤ)`. Rewrite `h1` using `[← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]`. Establish `hr : Module.finrank ℤ (𝓞 E) ≠ 0`. Rewrite using `[NumberField.RingOfIntegers.rank]`.

Conclude with `Module.finrank_pos.ne'`. Rewrite `h1` using `[isUnit_pow_iff hr, Int.isUnit_iff]`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `hd.one_lt.ne' (by exact_mod_cast h1)`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_isUnit_natCast {E : Type} [Field E] [NumberField E] {d : ℕ} (hd : d.Prime) : ¬ IsUnit (d : 𝓞 E) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
  rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap] at h1
  have hr : Module.finrank ℤ (𝓞 E) ≠ 0 := by
    rw [NumberField.RingOfIntegers.rank]; exact Module.finrank_pos.ne'
  rw [isUnit_pow_iff hr, Int.isUnit_iff] at h1
  rcases h1 with h1 | h1
  · exact hd.one_lt.ne' (by exact_mod_cast h1)
  · omega

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hwi : IsIntegral ℤ w`. Use `IsIntegral.of_pow (n := 2) two_pos ?_` and prove the remaining obligations. Rewrite using `[hw]`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d : ℤ))).neg`.

Set `W : 𝓞 E` to `⟨w, hwi⟩`. Establish `hW : W ^ 2 = -(d : 𝓞 E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `hw`.

Take `⟨P, hPmax, hPd⟩` from `Ideal.exists_le_maximal (Ideal.span {(d : 𝓞 E)}) ((Ideal.span_singleton_ne_top (not_isUnit_natCast hd)))`. Establish `hdP : (d : 𝓞 E) ∈ P` using `hPd (Ideal.mem_span_singleton_self _)`. Use `haveI := hPmax.isPrime`. Establish `he` using `(GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hd).1 h P hPmax.isPrime hdP`. Apply `GlobalTheory.Mem.RaySplit.not_mem_sq hd hdP he` to reduce the goal to its premises.

Establish `hWP : W ∈ P` using `hPmax.isPrime.mem_of_pow_mem 2 (by rw [hW]; exact P.neg_mem hdP)`. Establish `h2 : W ^ 2 ∈ P ^ 2` using `Ideal.pow_mem_pow hWP 2`. Rewrite `h2` using `[hW]`. Simplify using `using (P ^ 2).neg_mem h2`.
-/
theorem dvd_discr_of_sq {E : Type} [Field E] [NumberField E] {d : ℕ} (hd : d.Prime) {w : E} (hw : w ^ 2 = -(d : E)) :
    (d : ℤ) ∣ discr E := by
  by_contra h
  have hwi : IsIntegral ℤ w := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hw]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d : ℤ))).neg
  let W : 𝓞 E := ⟨w, hwi⟩
  have hW : W ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hw
  obtain ⟨P, hPmax, hPd⟩ := Ideal.exists_le_maximal (Ideal.span {(d : 𝓞 E)})
    ((Ideal.span_singleton_ne_top (not_isUnit_natCast hd)))
  have hdP : (d : 𝓞 E) ∈ P := hPd (Ideal.mem_span_singleton_self _)
  haveI := hPmax.isPrime
  have he := (GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hd).1 h P hPmax.isPrime hdP
  apply GlobalTheory.Mem.RaySplit.not_mem_sq hd hdP he
  have hWP : W ∈ P := hPmax.isPrime.mem_of_pow_mem 2 (by rw [hW]; exact P.neg_mem hdP)
  have h2 : W ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hWP 2
  rw [hW] at h2
  simpa using (P ^ 2).neg_mem h2

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hc : IsCoprime (p : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)`. Take `⟨u, t, h⟩` from `hc.map (Int.castRingHom A)`. Apply `hv.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← h]`.

Simplify using `only [map_natCast] at *`. Conclude with `v.add_mem (v.mul_mem_left _ hpv) (v.mul_mem_left _ hqv)`.
-/
theorem prime_eq_of_mem {A : Type} [CommRing A] {v : Ideal A} (hv : v.IsPrime) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpv : (p : A) ∈ v) (hqv : (q : A) ∈ v) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨u, t, h⟩ := hc.map (Int.castRingHom A)
  apply hv.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  simp only [map_natCast] at *
  exact v.add_mem (v.mul_mem_left _ hpv) (v.mul_mem_left _ hqv)

open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (c_vp delta_vp IsFieldData) in

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨w, hw, -⟩` from `hF.2.2.2.2.2.2.2`. Establish `hdd` using `dvd_discr_of_sq hF.1 hw`. Use `haveI : Fact l.Prime := ⟨hF.1⟩`. Unfold `c_vp at hc`.

Use `split_ifs at hc with hv`. Take `⟨v, hlv, hvf⟩` from `hv`. Take `⟨-, -, l', hl', -, hl'v, hnd, -⟩` from `h𝔣.2.2 v hvf`. Take `rfl` from `prime_eq_of_mem v.isPrime hl' hF.1 hl'v hlv`. Conclude with `hnd hdd`.

Unfold `delta_vp at hc`. Establish `hfr : (Module.finrank ℚ E : ℝ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Rewrite `hc` using `[div_eq_zero_iff, or_iff_left hfr, Nat.cast_eq_zero]`. Use `(padicValInt_dvd_iff (p := l) 1 (discr E)).1 (by simpa using hdd)` as an intermediate fact. Break down `this with h0 | h1` into its components or cases.

Conclude with `discr_ne_zero E h0`. Use linear arithmetic over natural numbers and integers.
-/
theorem ne_d_of_c_eq_zero {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {d : ℕ} {φ : I → E →+* ℂ}
    (hF : IsFieldData d φ) {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) {l : ℕ} (hc : c_vp 𝔣 l = 0) : l ≠ d := by
  rintro rfl
  obtain ⟨w, hw, -⟩ := hF.2.2.2.2.2.2.2
  have hdd := dvd_discr_of_sq hF.1 hw
  haveI : Fact l.Prime := ⟨hF.1⟩
  unfold c_vp at hc
  split_ifs at hc with hv
  · obtain ⟨v, hlv, hvf⟩ := hv
    obtain ⟨-, -, l', hl', -, hl'v, hnd, -⟩ := h𝔣.2.2 v hvf
    obtain rfl := prime_eq_of_mem v.isPrime hl' hF.1 hl'v hlv
    exact hnd hdd
  · unfold delta_vp at hc
    have hfr : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    rw [div_eq_zero_iff, or_iff_left hfr, Nat.cast_eq_zero] at hc
    have := (padicValInt_dvd_iff (p := l) 1 (discr E)).1 (by simpa using hdd)
    rcases this with h0 | h1
    · exact discr_ne_zero E h0
    · omega

/- English proof (translation)
Establish `hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j)`. Introduce `i j hij`. Take `⟨k, -, hk⟩` from `h (φ i)`. Establish `e : i = j` using `(hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm`. Substitute `e` using the available equality.

Establish `hr : ComplexEmbedding.IsReal (φ i)` using `ComplexEmbedding.isReal_iff.mpr hij.symm`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i))) (InfinitePlace.isReal_mk_iff.mpr hr)`. Establish `hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i) (j | j) hij`.

Simplify using `only [Sum.elim_inl] at hij`. Take `⟨k, -, hk⟩` from `h (φ i)`. Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl hij)]`. Conclude with `absurd hij (hreal i j)`. Conclude with `absurd hij.symm (hreal j i)`.

Simplify using `only [Sum.elim_inr] at hij`. Establish `hij' : φ i = φ j`. Simplify using `using congrArg ComplexEmbedding.conjugate hij`. Take `⟨k, -, hk⟩` from `h (φ i)`. Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl hij')]`.

Introduce `σ`. Take `⟨k, hk, -⟩` from `h σ`. Break down `hk with hk | hk` into its components or cases. Conclude with `⟨Sum.inl k, hk.symm⟩`. Conclude with `⟨Sum.inr k, hk.symm⟩`.

Establish `h1` using `Fintype.card_of_bijective hbij`. Rewrite `h1` using `[Fintype.card_sum, NumberField.Embeddings.card E ℂ]`. Establish `h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E)`. Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1`. Rewrite using `[Nat.cast_sub hk]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]`. Rewrite using `[this, Real.Gamma_nat_eq_factorial]`. Consider the case `succ n ih`. Establish `hpos : (k : ℝ) + n ≠ 0`. Establish `: (1 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Check the signs of the components of the expression. Rewrite using `[Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

/- English proof (translation)
Use `⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[Multiset.count_replicate]`.

Simplify using `[hj]`. Simplify using the standard rewrite rules.
-/
theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

/- English proof (translation)
Establish `hk : 1 ≤ 2 * s` using `by omega`. Rewrite using `[cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

/- English proof (translation)
Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

/- English proof (translation)
Simplify using `only [inv_div, div_pow, pow_add, pow_mul, mul_pow]`. Establish `h1 : a ^ n ≠ 0` using `pow_ne_zero _ ha`. Establish `h2 : b ^ n ≠ 0` using `pow_ne_zero _ hb`. Establish `h3 : r ^ n ≠ 0` using `pow_ne_zero _ hr`. Establish `h4 : Ω ^ k ≠ 0` using `pow_ne_zero _ hΩ`.

Establish `h5 : (Ω ^ 2) ^ n ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hΩ)`. Establish `h6 : a ^ k ≠ 0` using `pow_ne_zero _ ha`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_factor (a b Ω r π : ℂ) (k n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hΩ : Ω ≠ 0) (hr : r ≠ 0) (hpi : π ≠ 0) :
    (b / a) ^ n / a ^ k * (((a * b * r / (2 * π))⁻¹) ^ n * (a / Ω) ^ (k + 2 * n)) =
      (2 * π / r) ^ n / Ω ^ (k + 2 * n) := by
  simp only [inv_div, div_pow, pow_add, pow_mul, mul_pow]
  have h1 : a ^ n ≠ 0 := pow_ne_zero _ ha
  have h2 : b ^ n ≠ 0 := pow_ne_zero _ hb
  have h3 : r ^ n ≠ 0 := pow_ne_zero _ hr
  have h4 : Ω ^ k ≠ 0 := pow_ne_zero _ hΩ
  have h5 : (Ω ^ 2) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hΩ)
  have h6 : a ^ k ≠ 0 := pow_ne_zero _ ha
  field_simp
  ring

open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp betaBound_vp c_vp cE_vp a0 n_vp) in

/- English proof (translation)
Introduce `hSt hJ E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc κ S hS`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Establish `hld : l ≠ d` using `ne_d_of_c_eq_zero hF h𝔣 hc`. Rewrite using `[GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding]`. Introduce `lam`.

Take `⟨Ω, hΩ⟩` from `IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)`. Establish `hΩ0 : Ω ≠ 0`. Introduce and unpack `rfl`. Conclude with `latDisc_ne_zero Λ (by rw [← hΩ]; simp)`. Take `⟨a, b, hab, hT⟩` from `hJ E I d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ`.

Establish `hCM : IsCMType φ` using `hF.2.2.2.2.2.2.1`. Establish `hcard` using `card_eq_finrank hCM`. Establish `hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E)` using `hcard ▸ hF.2.2.2.2.2.1`. Establish `hc0 : condQ 𝔣 Q ≠ ⊥` using `by show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0`. Conclude with `mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)`.

Take `⟨⟨g, hg⟩, hD⟩` from `(((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1`. Take `⟨u, hu⟩` from `exists_list_count κ`. Establish `hDg` using `((hD g hg).2 κ u hu).1 S hS`. Establish `hTg` using `hT g κ u hg hu`. Rewrite `hTg` using `[hc]`.

Simplify using `only [mul_zero, add_zero] at hTg`. Establish `hp : ∀ i, Sz l lam 0 (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹`. Introduce `i`. Use `(hab i).2.2.2` as an intermediate fact. Rewrite `this` using `[hc, if_neg hld, add_zero]`. Then use the resulting hypothesis.

Establish `hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hF.1.pos)`. Conclude with `this.ne'` after adjusting the coercions. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hper : ∀ i, (b i / a i) ^ κ i / a i ^ (2 * s) * (((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i * (a i / Ω) ^ (2 * s + 2 * κ i)) = (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i)`.

Introduce `i`. Conclude with `per_factor _ _ _ _ _ _ _ (hab i).1 (hab i).2.1 hΩ0 hsd hpi`. Establish `hX : ((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ = (-1) ^ (∑ i, κ i) * ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))) * ∏ i, (((a i * b i * ((Real.sqrt d : ℝ) …`. Establish `hQF` using `Finset.prod_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => hper i)`. Establish `hR : ∏ i, (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) = (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) / Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i)`.

Rewrite using `[Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]`. Establish `hM : Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ = Fintype.card I • (2 * s) + 2 * ∑ i, κ i`. Simplify using `[Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK, mul_comm]`. Establish `hsq : ((-1 : ℂ) ^ (∑ i, κ i)) * (-1) ^ (∑ i, κ i) = 1`. Rewrite using `[← mul_pow]`.

Evaluate the numerical expressions. Rewrite using `[hDg, risingFactor_eq, cmPeriodConstant_eq_of_card_cmType hcard d s hs κ, hM]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hR, ← hQF, Finset.prod_mul_distrib]`. Take the linear combination `(-(((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) * (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 * (∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s))) * (∏ i, (((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) …`.

Establish `hSzX : Sz l lam (betaBound_vp d s κ 𝔣 z l / 12) (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ)`. Rewrite using `[hX, mul_assoc]`. Use `sz_neg_one_pow_mul _ (sz_mono (sz_mul hTg (sz_prod Finset.univ (fun i => ((κ i : ℕ) : ℝ) * 0 + ((2 * s + 2 * κ i : ℕ) : ℝ) * (a0 𝔣 l : ℝ)) _ (fun i _ => sz_mul (sz_pow (hp i) _) (sz_pow (hab i).2.2.1 _)))) (le_of_eq ?_))` and prove the remaining obligations. Simplify using `only [betaBound_vp, n_vp, if_pos hc, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]`. Use `push_cast`.

Simplify using `only [mul_zero, zero_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hβ : beta E d s κ Λ (S 0) = (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12`. Rewrite using `[beta, div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm 12]`. Rewrite using `[hβ]`.

Use `sz_pow hSzX 12 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latIntUnr : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetInt → LatIntUnr := by
  intro hSt hJ E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc κ S hS
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  have hld : l ≠ d := ne_d_of_c_eq_zero hF h𝔣 hc
  rw [GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding]
  intro lam
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  obtain ⟨a, b, hab, hT⟩ := hJ E I d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  have hCM : IsCMType φ := hF.2.2.2.2.2.2.1
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := hcard ▸ hF.2.2.2.2.2.1
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  have hTg := hT g κ u hg hu
  rw [hc] at hTg
  simp only [mul_zero, add_zero] at hTg
  have hp : ∀ i, Sz l lam 0 (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
    intro i
    have := (hab i).2.2.2
    rwa [hc, if_neg hld, add_zero] at this
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hF.1.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hper : ∀ i, (b i / a i) ^ κ i / a i ^ (2 * s) *
      (((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
        (a i / Ω) ^ (2 * s + 2 * κ i)) =
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) := by
    intro i
    exact per_factor _ _ _ _ _ _ _ (hab i).1 (hab i).2.1 hΩ0 hsd hpi
  have hX : ((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ =
      (-1) ^ (∑ i, κ i) * ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 *
        ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))) *
        ∏ i, (((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
          (a i / Ω) ^ (2 * s + 2 * κ i)) := by
    have hQF := Finset.prod_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => hper i)
    have hR : ∏ i, (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) =
        (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) / Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
    have hM : Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ = Fintype.card I • (2 * s) + 2 * ∑ i, κ i := by
      simp [Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK, mul_comm]
    have hsq : ((-1 : ℂ) ^ (∑ i, κ i)) * (-1) ^ (∑ i, κ i) = 1 := by
      rw [← mul_pow]; norm_num
    rw [hDg, risingFactor_eq, cmPeriodConstant_eq_of_card_cmType hcard d s hs κ, hM]
    calc _ = ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          ((2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) /
            Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i)) := by
            push_cast; ring
      _ = _ := by
        rw [← hR, ← hQF, Finset.prod_mul_distrib]
        linear_combination (-(((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          (∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s))) *
          (∏ i, (((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
              (a i / Ω) ^ (2 * s + 2 * κ i))))) * hsq
  have hSzX : Sz l lam (betaBound_vp d s κ 𝔣 z l / 12)
      (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) := by
    rw [hX, mul_assoc]
    refine sz_neg_one_pow_mul _ (sz_mono (sz_mul hTg (sz_prod Finset.univ
      (fun i => ((κ i : ℕ) : ℝ) * 0 + ((2 * s + 2 * κ i : ℕ) : ℝ) * (a0 𝔣 l : ℝ)) _
      (fun i _ => sz_mul (sz_pow (hp i) _) (sz_pow (hab i).2.2.1 _)))) (le_of_eq ?_))
    simp only [betaBound_vp, n_vp, if_pos hc, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]
    push_cast
    simp only [mul_zero, zero_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have hβ : beta E d s κ Λ (S 0) = (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
    rw [beta, div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm 12]
  rw [hβ]
  convert sz_pow hSzX 12 using 1
  push_cast
  ring

end GlobalTheory.LatValUnr
