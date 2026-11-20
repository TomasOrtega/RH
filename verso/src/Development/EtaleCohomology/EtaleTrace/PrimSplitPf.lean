import Development.EtaleCohomology.EtaleTrace.TwZeroPfSplit

noncomputable section
open Polynomial

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem ps_isUnit_of_quot {A : Type} [CommRing A] (x : A)
    (h : ∀ m : Ideal A, m.IsMaximal → Ideal.Quotient.mk m x ≠ 0) : IsUnit x := by
  by_contra hx
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.2 hxm)

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem ps_aeval_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : A) (p : ℤ[X]) :
    aeval (f x) p = f (aeval x p) := by
  have := Polynomial.aeval_algHom_apply f.toIntAlgHom x p
  simpa using this

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ps_prim_field {q : ℕ} {K : Type} [Field K] [NeZero (q : K)] {x : K}
    (h2 : aeval x (cyclotomic q ℤ) = 0) : IsPrimitiveRoot x q := by
  refine (Polynomial.isRoot_cyclotomic_iff).1 ?_
  rw [Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic_int, Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def]
  exact h2

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ps_pow_q {q : ℕ} {A : Type} [CommRing A] {ζ : A} (hζ : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp only [map_sub, map_pow, aeval_X, map_one, map_mul, hζ, zero_mul] at this
  exact sub_eq_zero.1 this

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Treat this case separately. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ps_pow_eq {A : Type} [CommRing A] {e x y : A} (h : e * x = e * y) (n : ℕ) : e * x ^ n = e * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, mul_comm (y ^ n), ← mul_assoc, h]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ps_aeval_eq {A : Type} [CommRing A] {e x y : A} (h : e * x = e * y) (p : ℤ[X]) :
    e * aeval x p = e * aeval y p := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, mul_smul_comm, ps_pow_eq h]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Substitute using the available equality.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem PrimSplit_of : PrimSplit := fun q _ A _ ζ ξ => ps_split ζ.2.1 ζ.2.2 ξ.2.2

end LateralTheory.EtaleTrace
