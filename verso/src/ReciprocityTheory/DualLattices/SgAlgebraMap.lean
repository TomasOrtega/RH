import ReciprocityTheory.DualLattices.EigPowEqOne
import ReciprocityTheory.DualLattices.IsAdicCompleteOfBasis

noncomputable section

open Finset Matrix Polynomial

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Use `haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)`. Establish `hm : (ρ (algebraMap ℤ_[p] O z)).map (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] (Matrix n n R) z`. Use extensionality with `i k`. Rewrite using `[AlgHom.commutes, Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h` using `heig (algebraMap ℤ_[p] O z) j`. Rewrite `h` using `[hm, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← algebraMap_smul R z (εT j)]`. Establish `h2 : (algebraMap ℤ_[p] R z - sg j (algebraMap ℤ_[p] O z)) • εT j = 0`. Rewrite using `[sub_smul, h, sub_self]`. Break down `smul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `(sub_eq_zero.mp h3).symm`. Conclude with `absurd h3 hj`.
-/
theorem sg_algebraMap (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (z : ℤ_[p]) : sg j (algebraMap ℤ_[p] O z) = algebraMap ℤ_[p] R z := by
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  have hm : (ρ (algebraMap ℤ_[p] O z)).map (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] (Matrix n n R) z := by
    ext i k
    rw [AlgHom.commutes, Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have h := heig (algebraMap ℤ_[p] O z) j
  rw [hm, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← algebraMap_smul R z (εT j)] at h
  have h2 : (algebraMap ℤ_[p] R z - sg j (algebraMap ℤ_[p] O z)) • εT j = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 hj

/- English proof (translation)
Establish `hc : (sg j).comp (algebraMap ℤ_[p] O) = algebraMap ℤ_[p] R` using `RingHom.ext fun z => sg_algebraMap hv ρ εT sg heig j hj z`. Rewrite using `[Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hc]`.
-/
theorem sg_aeval (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (a : O) (Q : ℤ_[p][X]) : sg j (aeval a Q) = aeval (sg j a) Q := by
  have hc : (sg j).comp (algebraMap ℤ_[p] O) = algebraMap ℤ_[p] R :=
    RingHom.ext fun z => sg_algebraMap hv ρ εT sg heig j hj z
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hc]

/- English proof (translation)
Establish `hpr : p.Prime` using `Fact.out`. Use `isDomain hv` as an intermediate fact. Set `_ : Field (R ⧸ mI hv)` to `instField hv`. Establish `hch : CharP (R ⧸ mI hv) p` using `charP p hv hpv`. Use `set f : ℤ_[p][X] := (ρ a).charpoly with hfdef`.

Establish `hf : f.Monic` using `Matrix.charpoly_monic _`. Establish `hfa : aeval (ρ a) f = 0` using `Matrix.aeval_self_charpoly _`. Set `S` to `AdjoinRoot f`. Set `J : Ideal S` to `Ideal.span {(p : S)}`. Establish `: Finite (S ⧸ J)` using `finite_quot f hf`.

Set `r : S` to `AdjoinRoot.root f + (c : S)`. Set `xq : S ⧸ J` to `Ideal.Quotient.mk J r`. Take `⟨M, hM0, hM⟩` from `exists_pow_idem xq`. Take `⟨N, rfl⟩ : ∃ N, M = N + 1` from `⟨M - 1, by omega⟩`. Set `uq : S ⧸ J` to `xq ^ (N + 1 + 1) + 1 - xq ^ (N + 1)`.

Establish `huq : IsUnit uq`. Use `IsUnit.of_mul_eq_one (xq ^ N * xq ^ (N + 1) + 1 - xq ^ (N + 1)) ?_` and prove the remaining obligations. Establish `he : xq ^ (N + 1) * xq ^ (N + 1) = xq ^ (N + 1)` using `by rw [← pow_add, ← hM]; ring_nf`. Establish `hx : xq * xq ^ N = xq ^ (N + 1)` using `by ring`. Simplify using `only [uq]`.

Take the linear combination `(xq * xq ^ N - xq - xq ^ N + 2) * he + xq ^ (N + 1) * hx`. Establish `hU : Nat.card (S ⧸ J)ˣ ≠ 0` using `Nat.card_pos.ne'`. Take `⟨s, m0, hm0p, hUeq⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hU p hpr.one_lt.ne'`. Establish `hm0 : 0 < m0` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hUeq; exact hU hUeq)`. Establish `hw : (uq ^ p ^ s) ^ m0 = 1`.

Establish `h1` using `pow_card_eq_one' (x := huq.unit)`. Rewrite `h1` using `[hUeq, pow_mul]`. Use `congrArg (fun u : (S ⧸ J)ˣ => (u : S ⧸ J)) h1` as an intermediate fact. Simplify using `using this`. Set `Q0 : ℤ_[p][X]` to `((X + (c : ℤ_[p][X])) ^ (N + 1 + 1) + 1 - (X + (c : ℤ_[p][X])) ^ (N + 1)) ^ p ^ s`.

Establish `hQ0 : AdjoinRoot.mk f Q0 = (r ^ (N + 1 + 1) + 1 - r ^ (N + 1)) ^ p ^ s`. Simplify using `[Q0, r]`. Establish `hH0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m0 - 1) = (p : S) * AdjoinRoot.mk f K`. Establish `hmem : AdjoinRoot.mk f (Q0 ^ m0 - 1) ∈ J`. Establish `e1 : AdjoinRoot.mk f (Q0 ^ m0 - 1) = ((r ^ (N + 1 + 1) + 1 - r ^ (N + 1)) ^ p ^ s) ^ m0 - 1`.

Rewrite using `[map_sub, map_pow, hQ0, map_one]`. Rewrite using `[e1, ← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `only [map_pow, map_add, map_sub, map_one]`. Rewrite using `[sub_eq_zero]`. Conclude with `hw`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hmem`. Take `⟨K, rfl⟩` from `AdjoinRoot.mk_surjective t`. Conclude with `⟨K, by rw [← ht, mul_comm]⟩`. Take `⟨Q, K, hQdvd, hQK⟩` from `hensel f hf hm0 hm0p Q0 hH0`. Use `⟨aeval a Q, m0, s, hm0, hm0p, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨g, hg⟩` from `hQdvd`. Use `congrArg (aeval (ρ a)) hg` as an intermediate fact. Rewrite `this` using `[map_mul, hfa, zero_mul, map_sub, map_pow, map_one, sub_eq_zero]`. Rewrite using `[← aeval_algHom_apply, this]`. Introduce `j hj hres`.

Establish `hfj : f.eval₂ (algebraMap ℤ_[p] R) (sg j a) = 0`. Establish `h1` using `heig (aeval a f) j`. Rewrite `h1` using `[← aeval_algHom_apply, hfa, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, sg_aeval hv ρ εT sg heig j hj]`. Use `smul_cancel hv hj (h1.symm.trans (zero_smul R (εT j)).symm)` as an intermediate fact. Rewrite `this` using `[aeval_def]`. Then use the resulting hypothesis.

Set `ev : S →+* R` to `AdjoinRoot.lift (algebraMap ℤ_[p] R) (sg j a) hfj`. Establish `hevJ : ∀ t ∈ J, res hv (ev t) = 0`. Introduce `t ht`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.1 ht`. Rewrite using `[map_mul, map_natCast, map_mul, map_natCast]`.

Establish `: (p : R ⧸ mI hv) = 0`. Rewrite using `[← map_natCast (res hv)]`. Conclude with `(res_eq_zero hv _).2 hpv`. Rewrite using `[this, mul_zero]`. Establish `hevr : ev r = sg j a + c` using `by show ev (AdjoinRoot.root f + (c : S)) = _`.

Rewrite using `[map_add, map_intCast]`. Simplify using `only [ev]`. Rewrite using `[AdjoinRoot.lift_root]`. Establish `hb : sg j (aeval a Q) = ev (AdjoinRoot.mk f Q)`. Rewrite using `[sg_aeval hv ρ εT sg heig j hj, AdjoinRoot.lift_mk, aeval_def]`.

Use `set x := res hv (sg j a + c) with hxdef`. Establish `hxM : x ^ (N + 1) = 1`. Establish `hmem : r ^ (2 * (N + 1)) - r ^ (N + 1) ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, sub_eq_zero]`. Conclude with `hM`.

Establish `h0` using `hevJ _ hmem`. Rewrite `h0` using `[map_sub, map_pow, map_pow, hevr, map_sub, map_pow, map_pow, ← hxdef, sub_eq_zero, pow_mul', sq]`. Establish `hx0 : x ^ (N + 1) ≠ 0` using `pow_ne_zero _ hres`. Conclude with `mul_left_cancel₀ hx0 (h0.trans (mul_one _).symm)`. Establish `hdiff : AdjoinRoot.mk f Q - AdjoinRoot.mk f Q0 ∈ J`.

Rewrite using `[← map_sub, hQK]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`. Establish `h2` using `hevJ _ hdiff`. Rewrite `h2` using `[map_sub, map_sub, sub_eq_zero, hQ0]`. Establish `hT : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : A), φ ((z ^ (N + 1 + 1) + 1 - z ^ (N + 1)) ^ p ^ s) = (φ z ^ (N + 1 + 1) + 1 - φ z ^ (N + 1)) ^ p ^ s` using `by intros; simp`.

Rewrite using `[hb, h2, hT, hT, hevr, ← hxdef, pow_succ x (N + 1), hxM, one_mul, add_sub_cancel_right]`.
-/
theorem seed (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (a : O) (c : ℤ) :
    ∃ (b : O) (m s : ℕ), 0 < m ∧ ¬ p ∣ m ∧ ρ b ^ m = 1 ∧
      ∀ j, εT j ≠ 0 → res hv (sg j a + c) ≠ 0 → res hv (sg j b) = res hv (sg j a + c) ^ p ^ s := by
  classical
  have hpr : p.Prime := Fact.out
  have := isDomain hv
  let _ : Field (R ⧸ mI hv) := instField hv
  have hch : CharP (R ⧸ mI hv) p := charP p hv hpv
  set f : ℤ_[p][X] := (ρ a).charpoly with hfdef
  have hf : f.Monic := Matrix.charpoly_monic _
  have hfa : aeval (ρ a) f = 0 := Matrix.aeval_self_charpoly _
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  have : Finite (S ⧸ J) := finite_quot f hf
  let r : S := AdjoinRoot.root f + (c : S)
  let xq : S ⧸ J := Ideal.Quotient.mk J r
  obtain ⟨M, hM0, hM⟩ := exists_pow_idem xq
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  let uq : S ⧸ J := xq ^ (N + 1 + 1) + 1 - xq ^ (N + 1)
  have huq : IsUnit uq := by
    refine IsUnit.of_mul_eq_one (xq ^ N * xq ^ (N + 1) + 1 - xq ^ (N + 1)) ?_
    have he : xq ^ (N + 1) * xq ^ (N + 1) = xq ^ (N + 1) := by rw [← pow_add, ← hM]; ring_nf
    have hx : xq * xq ^ N = xq ^ (N + 1) := by ring
    simp only [uq]
    linear_combination (xq * xq ^ N - xq - xq ^ N + 2) * he + xq ^ (N + 1) * hx

  have hU : Nat.card (S ⧸ J)ˣ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, m0, hm0p, hUeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hU p hpr.one_lt.ne'
  have hm0 : 0 < m0 := Nat.pos_of_ne_zero (by rintro rfl; simp at hUeq; exact hU hUeq)
  have hw : (uq ^ p ^ s) ^ m0 = 1 := by
    have h1 := pow_card_eq_one' (x := huq.unit)
    rw [hUeq, pow_mul] at h1
    have := congrArg (fun u : (S ⧸ J)ˣ => (u : S ⧸ J)) h1
    simpa using this

  let Q0 : ℤ_[p][X] := ((X + (c : ℤ_[p][X])) ^ (N + 1 + 1) + 1 - (X + (c : ℤ_[p][X])) ^ (N + 1)) ^ p ^ s
  have hQ0 : AdjoinRoot.mk f Q0 = (r ^ (N + 1 + 1) + 1 - r ^ (N + 1)) ^ p ^ s := by
    simp [Q0, r]
  have hH0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m0 - 1) = (p : S) * AdjoinRoot.mk f K := by
    have hmem : AdjoinRoot.mk f (Q0 ^ m0 - 1) ∈ J := by
      have e1 : AdjoinRoot.mk f (Q0 ^ m0 - 1) = ((r ^ (N + 1 + 1) + 1 - r ^ (N + 1)) ^ p ^ s) ^ m0 - 1 := by
        rw [map_sub, map_pow, hQ0, map_one]
      rw [e1, ← Ideal.Quotient.eq_zero_iff_mem]
      simp only [map_pow, map_add, map_sub, map_one]
      rw [sub_eq_zero]
      exact hw
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    obtain ⟨K, rfl⟩ := AdjoinRoot.mk_surjective t
    exact ⟨K, by rw [← ht, mul_comm]⟩
  obtain ⟨Q, K, hQdvd, hQK⟩ := hensel f hf hm0 hm0p Q0 hH0
  refine ⟨aeval a Q, m0, s, hm0, hm0p, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hQdvd
    have := congrArg (aeval (ρ a)) hg
    rw [map_mul, hfa, zero_mul, map_sub, map_pow, map_one, sub_eq_zero] at this
    rw [← aeval_algHom_apply, this]
  · intro j hj hres

    have hfj : f.eval₂ (algebraMap ℤ_[p] R) (sg j a) = 0 := by
      have h1 := heig (aeval a f) j
      rw [← aeval_algHom_apply, hfa, Matrix.map_zero _ (map_zero _), Matrix.zero_mul,
        sg_aeval hv ρ εT sg heig j hj] at h1
      have := smul_cancel hv hj (h1.symm.trans (zero_smul R (εT j)).symm)
      rwa [aeval_def] at this
    let ev : S →+* R := AdjoinRoot.lift (algebraMap ℤ_[p] R) (sg j a) hfj
    have hevJ : ∀ t ∈ J, res hv (ev t) = 0 := by
      intro t ht
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_mul, map_natCast, map_mul, map_natCast]
      have : (p : R ⧸ mI hv) = 0 := by
        rw [← map_natCast (res hv)]; exact (res_eq_zero hv _).2 hpv
      rw [this, mul_zero]
    have hevr : ev r = sg j a + c := by
      show ev (AdjoinRoot.root f + (c : S)) = _
      rw [map_add, map_intCast]
      simp only [ev]
      rw [AdjoinRoot.lift_root]
    have hb : sg j (aeval a Q) = ev (AdjoinRoot.mk f Q) := by
      rw [sg_aeval hv ρ εT sg heig j hj, AdjoinRoot.lift_mk, aeval_def]
    set x := res hv (sg j a + c) with hxdef
    have hxM : x ^ (N + 1) = 1 := by
      have hmem : r ^ (2 * (N + 1)) - r ^ (N + 1) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, sub_eq_zero]
        exact hM
      have h0 := hevJ _ hmem
      rw [map_sub, map_pow, map_pow, hevr, map_sub, map_pow, map_pow, ← hxdef, sub_eq_zero,
        pow_mul', sq] at h0
      have hx0 : x ^ (N + 1) ≠ 0 := pow_ne_zero _ hres
      exact mul_left_cancel₀ hx0 (h0.trans (mul_one _).symm)
    have hdiff : AdjoinRoot.mk f Q - AdjoinRoot.mk f Q0 ∈ J := by
      rw [← map_sub, hQK]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have h2 := hevJ _ hdiff
    rw [map_sub, map_sub, sub_eq_zero, hQ0] at h2
    have hT : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : A),
        φ ((z ^ (N + 1 + 1) + 1 - z ^ (N + 1)) ^ p ^ s) =
          (φ z ^ (N + 1 + 1) + 1 - φ z ^ (N + 1)) ^ p ^ s := by
      intros; simp
    rw [hb, h2, hT, hT, hevr, ← hxdef, pow_succ x (N + 1), hxM, one_mul, add_sub_cancel_right]

/- English proof (translation)
Establish `hpr : p.Prime` using `Fact.out`. Set `_ : Field (R ⧸ mI hv)` to `instField hv`. Establish `hch : CharP (R ⧸ mI hv) p` using `charP p hv hpv`. Use `set yi := res hv (sg i a)`. Use `set yj := res hv (sg j a)`.

Establish `h10 : (1 : R ⧸ mI hv) ≠ 0` using `one_ne_zero`. Establish `h20 : (2 : R ⧸ mI hv) ≠ 0`. Introduce `h0`. Use `(CharP.cast_eq_zero_iff (R ⧸ mI hv) p 2).1 (by exact_mod_cast h0)` as an intermediate fact. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this)`.

Establish `hc : ∃ c : ℤ, yi + (c : R ⧸ mI hv) ≠ 0 ∧ yj + (c : R ⧸ mI hv) ≠ 0`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `h0` using `hno 0`. Establish `h1` using `hno 1`.

Establish `h2` using `hno 2`. Simplify using `only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, add_zero] at h0 h1 h2`. Distinguish the cases in `a0 : yi = 0`. Establish `b1` using `h1 (by rw [a0, zero_add]; exact h10)`. Establish `b2` using `h2 (by rw [a0, zero_add]; exact h20)`.

Conclude with `h10 (by linear_combination b2 - b1)`. Establish `b0` using `h0 a0`. Distinguish the cases in `a1 : yi + 1 = 0`. Establish `b2` using `h2 (fun e => h10 (by linear_combination e - a1))`. Conclude with `h20 (by linear_combination b2 - b0)`.

Establish `b1` using `h1 a1`. Conclude with `h10 (by linear_combination b1 - b0)`. Take `⟨c, hci, hcj⟩` from `hc`. Take `⟨b, m, s, hm0, hmp, hbm, hbres⟩` from `seed p hv hpv ρ εT sg heig a c`. Use `⟨b, m, hm0, hmp, hbm, fun heq => h ?_⟩` and prove the remaining obligations.

Establish `hri : res hv (sg i a + c) = yi + c` using `by rw [map_add, map_intCast]`. Establish `hrj : res hv (sg j a + c) = yj + c` using `by rw [map_add, map_intCast]`. Rewrite `heq` using `[hbres j hj (by rwa [hrj]), hbres i hi (by rwa [hri]), hri, hrj, ← pow_mul, mul_comm, pow_mul]`. Establish `hcfix : ∀ k : ℕ, ((c : R ⧸ mI hv)) ^ p ^ k = c`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_mul, ih]`. Use `map_intCast (frobenius (R ⧸ mI hv) p) c` as an intermediate fact.

Rewrite `this` using `[frobenius_def]`. Then use the resulting hypothesis. Establish `hrhs : (yi + c) ^ p ^ t = yi ^ p ^ t + c` using `by rw [add_pow_char_pow, hcfix]`. Rewrite `heq` using `[hrhs]`. Establish `hsub : (yj + c - (yi ^ p ^ t + c)) ^ p ^ s = 0`. Rewrite using `[sub_pow_char_pow, heq, sub_self]`.

Use `pow_eq_zero_iff (pow_ne_zero s hpr.ne_zero) |>.1 hsub` as an intermediate fact. Take the linear combination `this`.
-/
theorem pair (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (a : O) (t : ℕ)
    (i j : ι) (hi : εT i ≠ 0) (hj : εT j ≠ 0) (h : res hv (sg j a) ≠ res hv (sg i a) ^ p ^ t) :
    ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧ ρ b ^ m = 1 ∧
      res hv (sg j b) ≠ res hv (sg i b) ^ p ^ t := by
  have hpr : p.Prime := Fact.out
  let _ : Field (R ⧸ mI hv) := instField hv
  have hch : CharP (R ⧸ mI hv) p := charP p hv hpv
  set yi := res hv (sg i a)
  set yj := res hv (sg j a)
  have h10 : (1 : R ⧸ mI hv) ≠ 0 := one_ne_zero
  have h20 : (2 : R ⧸ mI hv) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (R ⧸ mI hv) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this)
  have hc : ∃ c : ℤ, yi + (c : R ⧸ mI hv) ≠ 0 ∧ yj + (c : R ⧸ mI hv) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h0 := hno 0
    have h1 := hno 1
    have h2 := hno 2
    simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, add_zero] at h0 h1 h2
    by_cases a0 : yi = 0
    · have b1 := h1 (by rw [a0, zero_add]; exact h10)
      have b2 := h2 (by rw [a0, zero_add]; exact h20)
      exact h10 (by linear_combination b2 - b1)
    · have b0 := h0 a0
      by_cases a1 : yi + 1 = 0
      · have b2 := h2 (fun e => h10 (by linear_combination e - a1))
        exact h20 (by linear_combination b2 - b0)
      · have b1 := h1 a1
        exact h10 (by linear_combination b1 - b0)
  obtain ⟨c, hci, hcj⟩ := hc
  obtain ⟨b, m, s, hm0, hmp, hbm, hbres⟩ := seed p hv hpv ρ εT sg heig a c
  refine ⟨b, m, hm0, hmp, hbm, fun heq => h ?_⟩
  have hri : res hv (sg i a + c) = yi + c := by rw [map_add, map_intCast]
  have hrj : res hv (sg j a + c) = yj + c := by rw [map_add, map_intCast]
  rw [hbres j hj (by rwa [hrj]), hbres i hi (by rwa [hri]), hri, hrj, ← pow_mul, mul_comm,
    pow_mul] at heq
  have hcfix : ∀ k : ℕ, ((c : R ⧸ mI hv)) ^ p ^ k = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih]
      have := map_intCast (frobenius (R ⧸ mI hv) p) c
      rwa [frobenius_def] at this
  have hrhs : (yi + c) ^ p ^ t = yi ^ p ^ t + c := by rw [add_pow_char_pow, hcfix]
  rw [hrhs] at heq
  have hsub : (yj + c - (yi ^ p ^ t + c)) ^ p ^ s = 0 := by
    rw [sub_pow_char_pow, heq, sub_self]
  have := pow_eq_zero_iff (pow_ne_zero s hpr.ne_zero) |>.1 hsub
  linear_combination this

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
