import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.StepScalarProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

/- English proof (translation)
Simplify using `[adj]`.
-/
theorem adj_apply' (x S : Module.End ℚ V) : adj x S = x * S - S * x := by
  simp [adj]

/- English proof (translation)
Establish `h1 : H * F = F * H - (F + F)`. Combine the equalities or inequalities in the displayed calculation. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp [hv]`.

Consider the case `succ i ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := H), h1]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, ih, map_smul]`. Use `push_cast`. Use `module`.
-/
theorem H_pow (F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hHF : H * F - F * H = -(F + F)) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, H ((F ^ i) v) = ((n : ℚ) - 2 * i) • (F ^ i) v := by
  have h1 : H * F = F * H - (F + F) := by
    calc H * F = (H * F - F * H) + F * H := by abel
      _ = F * H - (F + F) := by rw [hHF]; abel
  intro i
  induction i with
  | zero => simp [hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := H), h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, ih, map_smul]
    push_cast
    module

/- English proof (translation)
Establish `h1 : E * F = F * E + H`. Combine the equalities or inequalities in the displayed calculation. Establish `hH` using `H_pow F H v n hHF hv`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero`. Rewrite using `[pow_one, ← Module.End.mul_apply (f := E), h1]`. Simplify using `[hE, hv]`. Consider the case `succ i ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := E), h1]`.

Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, ih, map_smul, hH]`. Rewrite using `[← Module.End.mul_apply (f := F), ← pow_succ']`. Use `push_cast`. Use `module`.
-/
theorem E_pow (E F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, E ((F ^ (i + 1)) v) = (((i : ℚ) + 1) * ((n : ℚ) - i)) • (F ^ i) v := by
  have h1 : E * F = F * E + H := by
    calc E * F = (E * F - F * E) + F * E := by abel
      _ = F * E + H := by rw [hEF]; abel
  have hH := H_pow F H v n hHF hv
  intro i
  induction i with
  | zero =>
    rw [pow_one, ← Module.End.mul_apply (f := E), h1]
    simp [hE, hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := E), h1]
    simp only [LinearMap.add_apply, Module.End.mul_apply, ih, map_smul, hH]
    rw [← Module.End.mul_apply (f := F), ← pow_succ']
    push_cast
    module

/- English proof (translation)
Establish `hEp` using `E_pow E F H v n hEF hHF hE hv`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Use `⟨fun i hi => ?_, by simp⟩` and prove the remaining obligations.

Simplify using `using hT i hi`. Consider the case `succ k ih`. Take `⟨ih1, ih2⟩` from `ih`. Establish `hstep : ∀ y, (((adj E) ^ (k + 1)) T) y = E ((((adj E) ^ k) T) y) - (((adj E) ^ k) T) (E y)`. Introduce `y`.

Rewrite using `[pow_succ', Module.End.mul_apply, adj_apply']`. Simplify using `[Module.End.mul_apply]`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i', rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Rewrite using `[hstep, hEp, map_smul, ih1 i' (by omega), ih1 (i' + 1) (by omega)]`.

Simplify using the standard rewrite rules. Rewrite using `[hstep, hEp, map_smul, ih1 (k + 1) (by omega), ih2, smul_smul, Finset.prod_range_succ, Nat.factorial_succ]`. Simplify using `only [map_zero, zero_sub]`. Rewrite using `[← neg_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjE_pow (E F H T : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v)
    (hT : ∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) :
    ∀ k : ℕ, (∀ i, k < i → (((adj E) ^ k) T) ((F ^ i) v) = 0) ∧
      (((adj E) ^ k) T) ((F ^ k) v) =
        ((-1 : ℚ) ^ k * (k.factorial : ℚ) * ∏ t ∈ Finset.range k, ((n : ℚ) - t)) • T v := by
  have hEp := E_pow E F H v n hEF hHF hE hv
  intro k
  induction k with
  | zero =>
    refine ⟨fun i hi => ?_, by simp⟩
    simpa using hT i hi
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : ∀ y, (((adj E) ^ (k + 1)) T) y = E ((((adj E) ^ k) T) y) - (((adj E) ^ k) T) (E y) := by
      intro y
      rw [pow_succ', Module.End.mul_apply, adj_apply']
      simp [Module.End.mul_apply]
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hstep, hEp, map_smul, ih1 i' (by omega), ih1 (i' + 1) (by omega)]
      simp
    · rw [hstep, hEp, map_smul, ih1 (k + 1) (by omega), ih2, smul_smul, Finset.prod_range_succ,
        Nat.factorial_succ]
      simp only [map_zero, zero_sub]
      rw [← neg_smul]
      congr 1
      push_cast
      ring

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro S y`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `S y`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, adj_apply']`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφ, zero_sub]`. Rewrite using `[← Module.End.mul_apply (f := F), ← pow_succ', pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_adjF_pow (F : Module.End ℚ V) (φ : V →ₗ[ℚ] ℚ) (hφ : ∀ x, φ (F x) = 0) :
    ∀ (k : ℕ) (S : Module.End ℚ V) (y : V), φ ((((adj F) ^ k) S) y) = (-1 : ℚ) ^ k * φ (S ((F ^ k) y)) := by
  intro k
  induction k with
  | zero => intro S y; simp
  | succ k ih =>
    intro S y
    rw [pow_succ, Module.End.mul_apply, ih, adj_apply']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφ, zero_sub]
    rw [← Module.End.mul_apply (f := F), ← pow_succ', pow_succ]
    ring

/- English proof (translation)
Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Simplify using `only [zero_add, Finset.sum_range_one, pow_zero, Finset.prod_range_zero, one_mul, Finset.prod_range_one, Nat.cast_zero, sub_zero]`. Rewrite using `[Nat.factorial_succ j]`.

Establish `h : (j.factorial : ℚ) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ K ih`.

Rewrite using `[Finset.sum_range_succ, mul_add, ih]`. Establish `e1 : K + 1 + j + 1 = (K + j + 1) + 1` using `by ring`. Rewrite using `[e1, Nat.factorial_succ (K + j + 1), Finset.prod_range_succ _ (K + 1)]`. Establish `h : ((K + j + 1).factorial : ℚ) ≠ 0` using `by positivity`. Use `push_cast`.

Generalize the expression as in `((K + j + 1).factorial : ℚ) = f at h ⊢`. Generalize the expression as in `(∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) = P`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem partial_sum (n j : ℕ) :
    ∀ K : ℕ, ((n : ℚ) + j + 1) * ∑ k ∈ Finset.range (K + 1),
        (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) =
      1 + (-1 : ℚ) ^ K * (j.factorial : ℚ) * (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) /
        ((K + j + 1).factorial : ℚ) := by
  intro K
  induction K with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, Finset.prod_range_zero, one_mul, Finset.prod_range_one,
      Nat.cast_zero, sub_zero]
    rw [Nat.factorial_succ j]
    have h : (j.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : K + 1 + j + 1 = (K + j + 1) + 1 := by ring
    rw [e1, Nat.factorial_succ (K + j + 1), Finset.prod_range_succ _ (K + 1)]
    have h : ((K + j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    generalize ((K + j + 1).factorial : ℚ) = f at h ⊢
    generalize (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) = P
    field_simp
    ring

/- English proof (translation)
Introduce `V _ _ E F H T v φ n K j hEF hHF hE hv hnK hφ hT`. Establish `hA` using `adjE_pow E F H T v n hEF hHF hE hv hT`. Establish `hB` using `phi_adjF_pow F φ hφ`. Establish `hterm : ∀ k : ℕ, φ ((((adj F) ^ k * (adj E) ^ k) T) v) = (k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v)`. Introduce `k`.

Rewrite using `[Module.End.mul_apply, hB, (hA k).2, map_smul, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Establish `hP : ∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t) = 0` using `Finset.prod_eq_zero (i := n) (Finset.mem_range.2 (by omega)) (sub_self _)`. Establish `hS` using `partial_sum n j K`.

Simplify using `only [hP, mul_zero, zero_div, add_zero] at hS`. Simplify using `only [proj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul, hterm]`. Establish `hc : ∀ k : ℕ, coef j k * ((k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v)) = (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) * φ (T v)`. Introduce `k`. Establish `h1 : (k.factorial : ℚ) ≠ 0` using `by positivity`.

Establish `h2 : ((k + j + 1).factorial : ℚ) ≠ 0` using `by positivity`. Simplify using `only [coef]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [hc, ← Finset.sum_mul]`. Rewrite using `[mul_comm, ← mul_assoc, hS, one_mul]`.
-/
theorem stepScalar : StepScalar := by
  intro V _ _ E F H T v φ n K j hEF hHF hE hv hnK hφ hT
  have hA := adjE_pow E F H T v n hEF hHF hE hv hT
  have hB := phi_adjF_pow F φ hφ
  have hterm : ∀ k : ℕ, φ ((((adj F) ^ k * (adj E) ^ k) T) v) =
      (k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v) := by
    intro k
    rw [Module.End.mul_apply, hB, (hA k).2, map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hP : ∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t) = 0 :=
    Finset.prod_eq_zero (i := n) (Finset.mem_range.2 (by omega)) (sub_self _)
  have hS := partial_sum n j K
  simp only [hP, mul_zero, zero_div, add_zero] at hS
  simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
    hterm]
  have hc : ∀ k : ℕ, coef j k * ((k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v)) =
      (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) *
        φ (T v) := by
    intro k
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((k + j + 1).factorial : ℚ) ≠ 0 := by positivity
    simp only [coef]
    field_simp
  simp only [hc, ← Finset.sum_mul]
  rw [mul_comm, ← mul_assoc, hS, one_mul]

end GlobalTheory.LeviCut.StepScalarProof
