import Formalism.GaussValuationBounds.Statement
import Formalism.WachModuleLifts.WachModuleProofs.LemmaHLift

namespace Formalism.NOK

/- English proof (translation)
Introduce `A _ a X p N M z c hN hp hz`. Take `⟨α, β, rfl⟩` from `Ideal.mem_span_pair.mp hp`. Take `⟨q, hqd⟩ : ∃ q, q = (M + N - 1) / N` from `⟨_, rfl⟩`. Rewrite `hz` using `[← hqd]`. Establish `hq : M ≤ N * q`.

Establish `h1` using `Nat.div_add_mod (M + N - 1) N`. Establish `h2` using `Nat.mod_lt (M + N - 1) (by omega : 0 < N)`. Rewrite `h1` using `[← hqd]`. Generalize the expression as in `N * q = w at h1 ⊢`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[add_pow]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hci : c ≤ i`. Establish `hmem : (α * a) ^ i ∈ Ideal.span {a ^ c, X ^ M}`. Rewrite using `[show (α * a) ^ i = (α ^ i * a ^ (i - c)) * a ^ c by`.

Rewrite using `[mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hci]]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)`. Establish `hle : M ≤ N * (z - i)` using `le_trans hq (Nat.mul_le_mul_left _ (by omega))`. Establish `hmem : (β * X ^ N) ^ (z - i) ∈ Ideal.span {a ^ c, X ^ M}`.

Rewrite using `[show (β * X ^ N) ^ (z - i) = (β ^ (z - i) * X ^ (N * (z - i) - M)) * X ^ M by`. Rewrite using `[mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)`.
-/
theorem powMemSpanPow : PowContent := by
  intro A _ a X p N M z c hN hp hz
  obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨q, hqd⟩ : ∃ q, q = (M + N - 1) / N := ⟨_, rfl⟩
  rw [← hqd] at hz
  have hq : M ≤ N * q := by
    have h1 := Nat.div_add_mod (M + N - 1) N
    have h2 := Nat.mod_lt (M + N - 1) (by omega : 0 < N)
    rw [← hqd] at h1
    generalize N * q = w at h1 ⊢
    omega
  rw [add_pow]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hci : c ≤ i
  · have hmem : (α * a) ^ i ∈ Ideal.span {a ^ c, X ^ M} := by
      rw [show (α * a) ^ i = (α ^ i * a ^ (i - c)) * a ^ c by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hci]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)
  · have hle : M ≤ N * (z - i) := le_trans hq (Nat.mul_le_mul_left _ (by omega))
    have hmem : (β * X ^ N) ^ (z - i) ∈ Ideal.span {a ^ c, X ^ M} := by
      rw [show (β * X ^ N) ^ (z - i) = (β ^ (z - i) * X ^ (N * (z - i) - M)) * X ^ M by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)

/- English proof (translation)
Introduce `A _ ℓ X u p E M j r hM hE`. Rewrite using `[Ideal.mem_span_singleton, mul_pow, mul_pow, ← Finset.prod_pow, mul_assoc]`. Establish `h1 : X ^ M ∣ X ^ r` using `pow_dvd_pow X hM`. Establish `h2 : ∏ s ∈ Finset.range j, p s ^ E ∣ ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r` using `Finset.prod_dvd_prod_of_dvd _ _ fun s _ => by`. Rewrite using `[← pow_mul]`.

Conclude with `pow_dvd_pow _ hE`. Conclude with `Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _`.
-/
theorem powMemSpanOfLe : RelVanish := by
  intro A _ ℓ X u p E M j r hM hE
  rw [Ideal.mem_span_singleton, mul_pow, mul_pow, ← Finset.prod_pow, mul_assoc]
  have h1 : X ^ M ∣ X ^ r := pow_dvd_pow X hM
  have h2 : ∏ s ∈ Finset.range j, p s ^ E ∣ ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r :=
    Finset.prod_dvd_prod_of_dvd _ _ fun s _ => by
      rw [← pow_mul]
      exact pow_dvd_pow _ hE
  exact Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _

/- English proof (translation)
Establish `h2 : (ℓ - 1) * padicValNat ℓ r.factorial ≤ r`. Rewrite using `[sub_one_mul_padicValNat_factorial]`. Conclude with `Nat.sub_le _ _`. Establish `h1 : 1 ≤ ℓ` using `(Fact.out : ℓ.Prime).one_lt.le`. Establish `h3 : (((ℓ - 1) * padicValNat ℓ r.factorial : ℕ) : ℝ) ≤ r` using `by exact_mod_cast h2`.

Move the coercions through the operations in `[Nat.cast_sub h1] at h3`. Conclude with `h3`.
-/
private theorem prime_sub_one_mul_padicValNat_factorial_le (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    ((ℓ : ℝ) - 1) * (padicValNat ℓ r.factorial : ℝ) ≤ r := by
  have h2 : (ℓ - 1) * padicValNat ℓ r.factorial ≤ r := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have h1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  have h3 : (((ℓ - 1) * padicValNat ℓ r.factorial : ℕ) : ℝ) ≤ r := by exact_mod_cast h2
  push_cast [Nat.cast_sub h1] at h3
  exact h3

/- English proof (translation)
Introduce `ℓ _ hℓ E M j r hj`. Establish `hℓ' : (3 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hL0 : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1)` using `by positivity`. Establish `hsig : ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 < sigNOK ℓ E M j`.

Unfold `sigNOK`. Use `push_cast`. Conclude with `Nat.lt_floor_add_one _`. Establish `hleg` using `prime_sub_one_mul_padicValNat_factorial_le ℓ r`. Establish `hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1`.

Rewrite using `[Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]`. Prove the components needed by the constructor for the conclusion. Introduce `hr`. Establish `hr' : ((ℓ : ℝ) - 1) * r < E`. Establish `h` using `(Nat.cast_lt (α := ℝ)).2 hr`.

Move the coercions through the operations in `[hsub] at h`. Conclude with `h`. Establish `key : ((r + padicValNat ℓ r.factorial : ℕ) : ℝ) < sigNOK ℓ E M j`. Use `lt_of_le_of_lt ?_ hsig` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (by positivity)]`.

Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hleg hL0.le, mul_le_mul_of_nonneg_right hr'.le (by linarith : (0 : ℝ) ≤ ℓ)]`. Conclude with `key` after adjusting the coercions. Use `le_trans ?_ hsig.le` and prove the remaining obligations. Break down `le_or_gt (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) 0 with h | h` into its components or cases.

Rewrite using `[max_eq_left h, sub_zero, div_le_div_iff₀ hL0 (by positivity)]`. Establish `h' : ((ℓ : ℝ) - 1) * r ≤ E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)` using `by linarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ ℓ * ((ℓ : ℝ) - 1))]`. Rewrite using `[max_eq_right h.le]`. Establish `hneg : (ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2 < 0` using `by nlinarith`.

Establish `e : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) - (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) - ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 = (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) / ((ℓ : ℝ) - 1) ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hn : (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) / ((ℓ : ℝ) - 1) ^ 2 ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le) (sq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem truncationExponentBounds : SigNum := by
  intro ℓ _ hℓ E M j r hj
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hsig : ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 < sigNOK ℓ E M j := by
    unfold sigNOK
    push_cast
    exact Nat.lt_floor_add_one _
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  constructor
  · intro hr
    have hr' : ((ℓ : ℝ) - 1) * r < E := by
      have h := (Nat.cast_lt (α := ℝ)).2 hr
      push_cast [hsub] at h
      exact h
    have key : ((r + padicValNat ℓ r.factorial : ℕ) : ℝ) < sigNOK ℓ E M j := by
      refine lt_of_le_of_lt ?_ hsig
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hleg hL0.le, mul_le_mul_of_nonneg_right hr'.le (by linarith : (0 : ℝ) ≤ ℓ)]
    exact_mod_cast key
  · refine le_trans ?_ hsig.le
    rcases le_or_gt (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) 0 with h | h
    · rw [max_eq_left h, sub_zero, div_le_div_iff₀ hL0 (by positivity)]
      have h' : ((ℓ : ℝ) - 1) * r ≤ E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ ℓ * ((ℓ : ℝ) - 1))]
    · rw [max_eq_right h.le]
      have hneg : (ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2 < 0 := by nlinarith
      have e : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) - (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) -
          ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
          (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
            ((ℓ : ℝ) - 1) ^ 2 := by
        field_simp
        ring
      have hn : (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
          ((ℓ : ℝ) - 1) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le) (sq_nonneg _)
      linarith

/- English proof (translation)
Introduce `A _ ℓ _ hℓ X u p E M j hj hp r`. Use `set σ := sigNOK ℓ E M j with hσ`. Use `set v := padicValNat ℓ r.factorial with hv`. Use `set J := Ideal.span {(ℓ : A) ^ (r + v), X ^ M * ∏ s ∈ Finset.range j, p s ^ E} with hJ`. Establish `hmem1 : (ℓ : A) ^ (r + v) ∈ J` using `Ideal.subset_span (Set.mem_insert _ _)`.

Establish `hmem2 : X ^ M * ∏ s ∈ Finset.range j, p s ^ E ∈ J` using `Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))`. Distinguish the cases in `hA : r + v ≤ σ`. Rewrite using `[← Nat.sub_add_cancel hA, pow_add]`. Conclude with `J.mul_mem_right _ (J.mul_mem_left _ hmem1)`. Rewrite `hA` using `[not_le]`.

Establish `hℓ' : (3 : ℝ) ≤ ℓ` using `by exact_mod_cast hℓ`. Establish `hL0 : (0 : ℝ) < (ℓ : ℝ) - 1` using `by linarith`. Establish `hN0 : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1)` using `by positivity`. Establish `hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1)` using `by positivity`. Establish `hleg` using `prime_sub_one_mul_padicValNat_factorial_le ℓ r`.

Establish `hB` using `(truncationExponentBounds ℓ hℓ E M j r hj).2`. Establish `h1 : (r : ℝ) + v ≤ r * ℓ / ((ℓ : ℝ) - 1)`. Rewrite using `[le_div_iff₀ hL0]`. Use polynomial arithmetic with `[hleg]`. Establish `hσr : (σ : ℝ) < r + v` using `by exact_mod_cast hA`.

Establish `hmx : max 0 (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) = ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)`. Apply `max_eq_right` to reduce the goal to its premises. Assume the negation of the conclusion as `hneg`. Rewrite `hneg` using `[not_le]`. Rewrite `hB` using `[max_eq_left hneg.le]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hB` using `[hmx]`. Establish `hc : ((r + v - σ : ℕ) : ℝ) ≤ ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)`. Rewrite using `[Nat.cast_sub hA.le]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]`. Establish `hE : E ≤ (ℓ - 1) * r`. Establish `h0 : (0 : ℝ) ≤ ((r + v - σ : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Establish `: (E : ℝ) ≤ ((ℓ - 1) * r : ℕ)`. Move the coercions through the operations in `[hsub]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Distinguish the cases in `hMr : M ≤ r`.

Establish `hv'` using `powMemSpanOfLe A ℓ X u p E M j r hMr hE`. Establish `hle : Ideal.span {X ^ M * ∏ s ∈ Finset.range j, p s ^ E} ≤ J` using `Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem2)`. Conclude with `J.mul_mem_left _ (hle hv')`. Rewrite `hMr` using `[not_le]`. Take `⟨c, hcd⟩ : ∃ c, c = r + v - σ` from `⟨_, rfl⟩`.

Take `⟨z, hzd⟩ : ∃ z, z = (ℓ - 1) * r - E` from `⟨_, rfl⟩`. Rewrite `hc` using `[← hcd]`. Establish `hzr : (z : ℝ) = ((ℓ : ℝ) - 1) * r - E`. Rewrite using `[hzd, Nat.cast_sub hE]`. Move the coercions through the operations in `[hsub]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hN1 : 1 ≤ ℓ ^ (j - 1)` using `Nat.one_le_pow _ _ (by omega)`. Establish `hcz : c ≤ z`. Establish `: (c : ℝ) ≤ z` using `by rw [hzr]; linarith`. Conclude with `this` after adjusting the coercions.

Establish `hMN : M - r ≤ (z - c) * ℓ ^ (j - 1)`. Establish `hreal : ((M - r : ℕ) : ℝ) ≤ ((z - c : ℕ) : ℝ) * ((ℓ ^ (j - 1) : ℕ) : ℝ)`. Rewrite using `[Nat.cast_sub hMr.le, Nat.cast_sub hcz]`. Use `push_cast`. Establish `hdiv : (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ z - c` using `by rw [hzr]; linarith`.

Rewrite `hdiv` using `[div_le_iff₀ hN0]`. Establish `: (0 : ℝ) ≤ r` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hreal` after adjusting the coercions. Establish `hz : c + (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) ≤ z + 1`.

Establish `hlt : (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) < z - c + 1`. Rewrite using `[Nat.div_lt_iff_lt_mul (by omega), add_mul, one_mul]`. Generalize the expression as in `(z - c) * ℓ ^ (j - 1) = w at hMN ⊢`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Establish `hpz` using `powMemSpanPow A (ℓ : A) X (p (j - 1)) (ℓ ^ (j - 1)) (M - r) z c hN1 hp hz`. Take `⟨α, β, hαβ⟩` from `Ideal.mem_span_pair.mp hpz`. Establish `hprod : ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r = (∏ s ∈ Finset.range j, p s ^ E) * (p (j - 1) ^ z * ∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z)`. Rewrite using `[Finset.mul_prod_erase (Finset.range j) (fun s => p s ^ z) (Finset.mem_range.mpr (by omega)), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_mul, ← pow_add, hzd, Nat.add_sub_cancel' hE]`. Establish `hX : X ^ M = X ^ r * X ^ (M - r)` using `by rw [← pow_add, Nat.add_sub_cancel' hMr.le]`. Establish `hl : (ℓ : A) ^ (r + v) = (ℓ : A) ^ σ * (ℓ : A) ^ c`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_pow, mul_pow, ← Finset.prod_pow, hprod, ← hαβ]`. Use `J.add_mem (J.mul_mem_left (α * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * X ^ r * ∏ s ∈ Finset.range j, p s ^ E) hmem1) (J.mul_mem_left (β * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * (ℓ : A) ^ σ) hmem2) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hX, hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scaledPowMemSpan : RelCoeff := by
  intro A _ ℓ _ hℓ X u p E M j hj hp r
  set σ := sigNOK ℓ E M j with hσ
  set v := padicValNat ℓ r.factorial with hv
  set J := Ideal.span {(ℓ : A) ^ (r + v), X ^ M * ∏ s ∈ Finset.range j, p s ^ E} with hJ
  have hmem1 : (ℓ : A) ^ (r + v) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hmem2 : X ^ M * ∏ s ∈ Finset.range j, p s ^ E ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  by_cases hA : r + v ≤ σ
  · rw [← Nat.sub_add_cancel hA, pow_add]
    exact J.mul_mem_right _ (J.mul_mem_left _ hmem1)
  rw [not_le] at hA
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1) := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hB := (truncationExponentBounds ℓ hℓ E M j r hj).2
  have h1 : (r : ℝ) + v ≤ r * ℓ / ((ℓ : ℝ) - 1) := by
    rw [le_div_iff₀ hL0]
    nlinarith [hleg]
  have hσr : (σ : ℝ) < r + v := by exact_mod_cast hA
  have hmx : max 0 (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) =
      ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by
    apply max_eq_right
    by_contra hneg
    rw [not_le] at hneg
    rw [max_eq_left hneg.le] at hB
    linarith
  rw [hmx] at hB
  have hc : ((r + v - σ : ℕ) : ℝ) ≤ ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by
    rw [Nat.cast_sub hA.le]
    push_cast
    linarith
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  have hE : E ≤ (ℓ - 1) * r := by
    have h0 : (0 : ℝ) ≤ ((r + v - σ : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (E : ℝ) ≤ ((ℓ - 1) * r : ℕ) := by
      push_cast [hsub]
      linarith
    exact_mod_cast this
  by_cases hMr : M ≤ r
  · have hv' := powMemSpanOfLe A ℓ X u p E M j r hMr hE
    have hle : Ideal.span {X ^ M * ∏ s ∈ Finset.range j, p s ^ E} ≤ J :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem2)
    exact J.mul_mem_left _ (hle hv')
  rw [not_le] at hMr
  obtain ⟨c, hcd⟩ : ∃ c, c = r + v - σ := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z, z = (ℓ - 1) * r - E := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hzr : (z : ℝ) = ((ℓ : ℝ) - 1) * r - E := by
    rw [hzd, Nat.cast_sub hE]
    push_cast [hsub]
    ring
  have hN1 : 1 ≤ ℓ ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hcz : c ≤ z := by
    have : (c : ℝ) ≤ z := by rw [hzr]; linarith
    exact_mod_cast this
  have hMN : M - r ≤ (z - c) * ℓ ^ (j - 1) := by
    have hreal : ((M - r : ℕ) : ℝ) ≤ ((z - c : ℕ) : ℝ) * ((ℓ ^ (j - 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hMr.le, Nat.cast_sub hcz]
      push_cast
      have hdiv : (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ z - c := by rw [hzr]; linarith
      rw [div_le_iff₀ hN0] at hdiv
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      linarith
    exact_mod_cast hreal
  have hz : c + (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) ≤ z + 1 := by
    have hlt : (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) < z - c + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega), add_mul, one_mul]
      generalize (z - c) * ℓ ^ (j - 1) = w at hMN ⊢
      omega
    omega
  have hpz := powMemSpanPow A (ℓ : A) X (p (j - 1)) (ℓ ^ (j - 1)) (M - r) z c hN1 hp hz
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hpz
  have hprod : ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r = (∏ s ∈ Finset.range j, p s ^ E) *
      (p (j - 1) ^ z * ∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) := by
    rw [Finset.mul_prod_erase (Finset.range j) (fun s => p s ^ z) (Finset.mem_range.mpr (by omega)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← pow_mul, ← pow_add, hzd, Nat.add_sub_cancel' hE]
  have hX : X ^ M = X ^ r * X ^ (M - r) := by rw [← pow_add, Nat.add_sub_cancel' hMr.le]
  have hl : (ℓ : A) ^ (r + v) = (ℓ : A) ^ σ * (ℓ : A) ^ c := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← Finset.prod_pow, hprod, ← hαβ]
  convert J.add_mem (J.mul_mem_left (α * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * X ^ r *
      ∏ s ∈ Finset.range j, p s ^ E) hmem1)
    (J.mul_mem_left (β * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * (ℓ : A) ^ σ) hmem2) using 1
  rw [hX, hl]
  ring

end Formalism.NOK
