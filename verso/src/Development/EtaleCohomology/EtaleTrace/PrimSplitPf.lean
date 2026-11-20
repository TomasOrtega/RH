import Development.EtaleCohomology.EtaleTrace.TwZeroPfSplit

noncomputable section
open Polynomial

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Take `⟨m, hm, hxm⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)`. Conclude with `h m hm (Ideal.Quotient.eq_zero_iff_mem.2 hxm)`.
-/
theorem ps_isUnit_of_quot {A : Type} [CommRing A] (x : A)
    (h : ∀ m : Ideal A, m.IsMaximal → Ideal.Quotient.mk m x ≠ 0) : IsUnit x := by
  by_contra hx
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.2 hxm)

/- English proof (translation)
Use `Polynomial.aeval_algHom_apply f.toIntAlgHom x p` as an intermediate fact. Simplify using `using this`.
-/
theorem ps_aeval_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : A) (p : ℤ[X]) :
    aeval (f x) p = f (aeval x p) := by
  have := Polynomial.aeval_algHom_apply f.toIntAlgHom x p
  simpa using this

/- English proof (translation)
Use `(Polynomial.isRoot_cyclotomic_iff).1 ?_` and prove the remaining obligations. Rewrite using `[Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic_int, Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def]`. Conclude with `h2`.
-/
theorem ps_prim_field {q : ℕ} {K : Type} [Field K] [NeZero (q : K)] {x : K}
    (h2 : aeval x (cyclotomic q ℤ) = 0) : IsPrimitiveRoot x q := by
  refine (Polynomial.isRoot_cyclotomic_iff).1 ?_
  rw [Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic_int, Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def]
  exact h2

/- English proof (translation)
Set `_ : Field (A ⧸ m)` to `Ideal.Quotient.field m`. Establish `: NeZero ((q : ℕ) : A ⧸ m)` using `⟨by`. Use `hq.map (Ideal.Quotient.mk m)` as an intermediate fact. Simplify using `using this.ne_zero⟩`. Establish `h2` using `ps_aeval_map (Ideal.Quotient.mk m) ζ (cyclotomic q ℤ)`.

Rewrite `h2` using `[hζ, map_zero]`. Conclude with `ps_prim_field h2`.
-/
theorem ps_prim_quot {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) (m : Ideal A) [m.IsMaximal] :
    IsPrimitiveRoot (Ideal.Quotient.mk m ζ) q := by
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have := hq.map (Ideal.Quotient.mk m)
    simpa using this.ne_zero⟩
  have h2 := ps_aeval_map (Ideal.Quotient.mk m) ζ (cyclotomic q ℤ)
  rw [hζ, map_zero] at h2
  exact ps_prim_field h2

/- English proof (translation)
Take `⟨g, hg⟩` from `Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ`. Use `congrArg (aeval ζ) hg` as an intermediate fact. Simplify using `only [map_sub, map_pow, aeval_X, map_one, map_mul, hζ, zero_mul] at this`. Conclude with `sub_eq_zero.1 this`.
-/
theorem ps_pow_q {q : ℕ} {A : Type} [CommRing A] {ζ : A} (hζ : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp only [map_sub, map_pow, aeval_X, map_one, map_mul, hζ, zero_mul] at this
  exact sub_eq_zero.1 this

/- English proof (translation)
Use `ps_isUnit_of_quot _ fun m hm => ?_` and prove the remaining obligations. Establish `hp` using `ps_prim_quot hq hζ m`. Introduce `h0`. Rewrite `h0` using `[map_sub, map_pow, map_one, sub_eq_zero]`. Establish `h1 : (Ideal.Quotient.mk m ζ) ^ k = 1`.

Use `congrArg (Ideal.Quotient.mk m) (congrArg (· ^ k) hw)` as an intermediate fact. Simplify using `only [mul_pow, one_pow, map_mul, map_pow, map_one] at this`. Rewrite `this` using `[h0, one_mul]`. Conclude with `this`. Use `Nat.le_of_dvd hk0 (hp.dvd_of_pow_eq_one k h1)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem ps_sub_one_unit {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ w : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) (hw : w * ζ = 1) {k : ℕ} (hk0 : 0 < k) (hkq : k < q) : IsUnit (w ^ k - 1) := by
  refine ps_isUnit_of_quot _ fun m hm => ?_
  have hp := ps_prim_quot hq hζ m
  intro h0
  rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
  have h1 : (Ideal.Quotient.mk m ζ) ^ k = 1 := by
    have := congrArg (Ideal.Quotient.mk m) (congrArg (· ^ k) hw)
    simp only [mul_pow, one_pow, map_mul, map_pow, map_one] at this
    rw [h0, one_mul] at this; exact this
  have := Nat.le_of_dvd hk0 (hp.dvd_of_pow_eq_one k h1)
  omega

/- English proof (translation)
Use `ps_isUnit_of_quot _ fun m hm => ?_` and prove the remaining obligations. Establish `hp` using `ps_prim_quot hq hζ m`. Introduce `h0`. Establish `h2` using `ps_aeval_map (Ideal.Quotient.mk m) (ζ ^ i) (cyclotomic q ℤ)`. Rewrite `h2` using `[h0, map_pow]`.

Set `_ : Field (A ⧸ m)` to `Ideal.Quotient.field m`. Establish `: NeZero ((q : ℕ) : A ⧸ m)` using `⟨by`. Use `hq.map (Ideal.Quotient.mk m)` as an intermediate fact. Simplify using `using this.ne_zero⟩`. Establish `hp2` using `ps_prim_field h2`.

Conclude with `hi ((hp.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 hp2)`.
-/
theorem ps_cyc_unit {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) {i : ℕ} (hi : ¬ Nat.Coprime i q) : IsUnit (aeval (ζ ^ i) (cyclotomic q ℤ)) := by
  refine ps_isUnit_of_quot _ fun m hm => ?_
  have hp := ps_prim_quot hq hζ m
  intro h0
  have h2 := ps_aeval_map (Ideal.Quotient.mk m) (ζ ^ i) (cyclotomic q ℤ)
  rw [h0, map_pow] at h2
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have := hq.map (Ideal.Quotient.mk m)
    simpa using this.ne_zero⟩
  have hp2 := ps_prim_field h2
  exact hi ((hp.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 hp2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, mul_comm (y ^ n), ← mul_assoc, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ps_pow_eq {A : Type} [CommRing A] {e x y : A} (h : e * x = e * y) (n : ℕ) : e * x ^ n = e * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, mul_comm (y ^ n), ← mul_assoc, h]; ring

/- English proof (translation)
Rewrite using `[Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, mul_smul_comm, ps_pow_eq h]`.
-/
theorem ps_aeval_eq {A : Type} [CommRing A] {e x y : A} (h : e * x = e * y) (p : ℤ[X]) :
    e * aeval x p = e * aeval y p := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, mul_smul_comm, ps_pow_eq h]

/- English proof (translation)
Establish `hq0 : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Take `⟨u, hu⟩` from `hq`. Use `set c : A := ((u⁻¹ : Aˣ) : A) with hcdef`. Establish `hc : c * q = 1` using `by rw [← hu, hcdef, Units.inv_mul]`. Establish `hζq` using `ps_pow_q hζ`.

Establish `hξq` using `ps_pow_q hξ`. Use `set w : A := ζ ^ (q - 1) with hwdef`. Establish `hw : w * ζ = 1` using `by rw [hwdef, ← pow_succ, Nat.sub_add_cancel hq0, hζq]`. Establish `hwq : w ^ q = 1` using `by rw [hwdef, ← pow_mul, mul_comm, pow_mul, hζq, one_pow]`. Set `η : Fin q → A` to `fun i => ξ * w ^ (i : ℕ)`.

Set `S : Fin q → A` to `fun i => ∑ k ∈ Finset.range q, (η i) ^ k`. Establish `hη : ∀ i, (η i) ^ q = 1` using `fun i => by`. Simplify using `only [η]`. Rewrite using `[mul_pow, hξq, ← pow_mul, mul_comm (i : ℕ) q, pow_mul, hwq, one_pow, one_mul]`. Establish `hSη : ∀ i, S i * η i = S i` using `fun i => by`.

Use `geom_sum_mul (η i) q` as an intermediate fact. Rewrite `this` using `[hη, sub_self, mul_sub, mul_one, sub_eq_zero]`. Conclude with `this`. Establish `hSpow : ∀ i k, S i * (η i) ^ k = S i` using `fun i k => by`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ← mul_assoc, ih, hSη]`. Establish `hSS : ∀ i, S i * S i = q * S i` using `fun i => by conv_lhs => rw [show S i * S i = S i * ∑ k ∈ Finset.range q, (η i) ^ k from rfl]`. Rewrite using `[Finset.mul_sum]`. Simplify using `only [hSpow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Use `⟨fun i => c * S i, fun i => ?_, ?_, fun i => ?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `show c * S i * (c * S i) = c * S i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum]`. Establish `hT : ∀ k ∈ Finset.range q, ∑ i : Fin q, ξ ^ k * (w ^ k) ^ (i : ℕ) = if k = 0 then (q : A) else 0`.

Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range]`. Rewrite using `[← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (w ^ k) ^ i)]`. Use `split_ifs with h0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Establish `hu2` using `ps_sub_one_unit (ζ := ζ) ⟨u, hu⟩ hζ hw (Nat.pos_of_ne_zero h0) hk`. Establish `hg : (∑ i ∈ Finset.range q, (w ^ k) ^ i) * (w ^ k - 1) = 0`. Rewrite using `[geom_sum_mul, ← pow_mul, mul_comm k q, pow_mul, hwq, one_pow, sub_self]`. Rewrite using `[(hu2.mul_left_eq_zero).1 hg, mul_zero]`.

Establish `hsum : ∑ i : Fin q, S i = (q : A)`. Simplify using `only [S, η]`. Rewrite using `[Finset.sum_comm]`. Establish `hT2 : ∀ k ∈ Finset.range q, ∑ x : Fin q, (ξ * w ^ (x : ℕ)) ^ k = if k = 0 then (q : A) else 0` using `fun k hk => by`. Rewrite using `[← hT k hk]; exact Finset.sum_congr rfl fun i _ => by ring`.

Rewrite using `[Finset.sum_congr rfl hT2]`. Rewrite using `[Finset.sum_ite_eq' (Finset.range q) 0, if_pos (Finset.mem_range.2 hq0)]`. Rewrite using `[hsum, hc]`. Establish `h1 : c * S i * η i = c * S i` using `by rw [mul_assoc, hSη]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1` using `ps_aeval_eq (e := c * S i) (x := ξ) (y := ζ ^ (i : ℕ)) ?_ (cyclotomic q ℤ)`. Rewrite `h1` using `[hξ, mul_zero]`. Conclude with `((ps_cyc_unit ⟨u, hu⟩ hζ hi).mul_left_eq_zero).1 h1.symm`. Establish `h1 : c * S i * η i = c * S i` using `by rw [mul_assoc, hSη]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ps_split {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ ξ : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) : ∃ e : Fin q → A,
    (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ = e i * ζ ^ (i : ℕ)) ∧
    (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨u, hu⟩ := hq
  set c : A := ((u⁻¹ : Aˣ) : A) with hcdef
  have hc : c * q = 1 := by rw [← hu, hcdef, Units.inv_mul]
  have hζq := ps_pow_q hζ
  have hξq := ps_pow_q hξ
  set w : A := ζ ^ (q - 1) with hwdef
  have hw : w * ζ = 1 := by rw [hwdef, ← pow_succ, Nat.sub_add_cancel hq0, hζq]
  have hwq : w ^ q = 1 := by rw [hwdef, ← pow_mul, mul_comm, pow_mul, hζq, one_pow]
  let η : Fin q → A := fun i => ξ * w ^ (i : ℕ)
  let S : Fin q → A := fun i => ∑ k ∈ Finset.range q, (η i) ^ k
  have hη : ∀ i, (η i) ^ q = 1 := fun i => by
    simp only [η]; rw [mul_pow, hξq, ← pow_mul, mul_comm (i : ℕ) q, pow_mul, hwq, one_pow, one_mul]
  have hSη : ∀ i, S i * η i = S i := fun i => by
    have := geom_sum_mul (η i) q
    rw [hη, sub_self, mul_sub, mul_one, sub_eq_zero] at this
    exact this
  have hSpow : ∀ i k, S i * (η i) ^ k = S i := fun i k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hSη]
  have hSS : ∀ i, S i * S i = q * S i := fun i => by
    conv_lhs => rw [show S i * S i = S i * ∑ k ∈ Finset.range q, (η i) ^ k from rfl]
    rw [Finset.mul_sum]
    simp only [hSpow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨fun i => c * S i, fun i => ?_, ?_, fun i => ?_, fun i hi => ?_⟩
  · show c * S i * (c * S i) = c * S i
    calc c * S i * (c * S i) = c * (c * (S i * S i)) := by ring
      _ = c * ((c * q) * S i) := by rw [hSS]; ring
      _ = c * S i := by rw [hc, one_mul]
  · rw [← Finset.mul_sum]
    have hT : ∀ k ∈ Finset.range q, ∑ i : Fin q, ξ ^ k * (w ^ k) ^ (i : ℕ) = if k = 0 then (q : A) else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (w ^ k) ^ i)]
      split_ifs with h0
      · subst h0; simp
      · have hu2 := ps_sub_one_unit (ζ := ζ) ⟨u, hu⟩ hζ hw (Nat.pos_of_ne_zero h0) hk
        have hg : (∑ i ∈ Finset.range q, (w ^ k) ^ i) * (w ^ k - 1) = 0 := by
          rw [geom_sum_mul, ← pow_mul, mul_comm k q, pow_mul, hwq, one_pow, sub_self]
        rw [(hu2.mul_left_eq_zero).1 hg, mul_zero]
    have hsum : ∑ i : Fin q, S i = (q : A) := by
      simp only [S, η]
      rw [Finset.sum_comm]
      have hT2 : ∀ k ∈ Finset.range q, ∑ x : Fin q, (ξ * w ^ (x : ℕ)) ^ k = if k = 0 then (q : A) else 0 :=
        fun k hk => by
          rw [← hT k hk]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl hT2]
      rw [Finset.sum_ite_eq' (Finset.range q) 0, if_pos (Finset.mem_range.2 hq0)]
    rw [hsum, hc]
  · have h1 : c * S i * η i = c * S i := by rw [mul_assoc, hSη]
    calc c * S i * ξ = c * S i * ξ * (w * ζ) ^ (i : ℕ) := by rw [hw, one_pow, mul_one]
      _ = c * S i * η i * ζ ^ (i : ℕ) := by simp only [η]; rw [mul_pow]; ring
      _ = c * S i * ζ ^ (i : ℕ) := by rw [h1]
  · have h1 := ps_aeval_eq (e := c * S i) (x := ξ) (y := ζ ^ (i : ℕ)) ?_ (cyclotomic q ℤ)
    · rw [hξ, mul_zero] at h1
      exact ((ps_cyc_unit ⟨u, hu⟩ hζ hi).mul_left_eq_zero).1 h1.symm
    · have h1 : c * S i * η i = c * S i := by rw [mul_assoc, hSη]
      calc c * S i * ξ = c * S i * ξ * (w * ζ) ^ (i : ℕ) := by rw [hw, one_pow, mul_one]
        _ = c * S i * η i * ζ ^ (i : ℕ) := by simp only [η]; rw [mul_pow]; ring
        _ = c * S i * ζ ^ (i : ℕ) := by rw [h1]

/- English proof (translation)
Introduce `q _ A _ ζ ξ` and use `ps_split ζ.2.1 ζ.2.2 ξ.2.2`.
-/
theorem PrimSplit_of : PrimSplit := fun q _ A _ ζ ξ => ps_split ζ.2.1 ζ.2.2 ξ.2.2

end LateralTheory.EtaleTrace
