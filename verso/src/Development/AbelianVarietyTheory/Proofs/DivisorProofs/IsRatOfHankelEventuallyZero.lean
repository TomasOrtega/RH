import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.Kron

open Polynomial

variable {F : Type} [Field F] (c : ℕ → F)

def ev : F[X] →ₗ[F] F := Polynomial.lsum fun i => c i • LinearMap.id

/- English proof (translation)
Simplify using `[ev, Polynomial.lsum_apply]`.
-/
theorem ev_monomial (n : ℕ) (a : F) : ev c (monomial n a) = c n * a := by
  simp [ev, Polynomial.lsum_apply]

/- English proof (translation)
Use `conv_lhs => rw [p.as_sum_range' n hp]`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← C_mul_X_pow_eq_monomial, show q * (C (p.coeff j) * X ^ j) = p.coeff j • (q * X ^ j) by`. Rewrite using `[smul_eq_C_mul]`.

Use the proof step `ring, map_smul, smul_eq_mul]`.
-/
theorem ev_expand (q p : F[X]) (n : ℕ) (hp : p.natDegree < n) :
    ev c (q * p) = ∑ j ∈ Finset.range n, p.coeff j * ev c (q * X ^ j) := by
  conv_lhs => rw [p.as_sum_range' n hp]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, show q * (C (p.coeff j) * X ^ j) = p.coeff j • (q * X ^ j) by
    rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[ev_expand c q p s hp]`. Conclude with `Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]`.
-/
theorem ev_zero_of_lt (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree < s) : ev c (q * p) = 0 := by
  rw [ev_expand c q p s hp]
  exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]

/- English proof (translation)
Rewrite using `[ev_expand c q p (s + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero], zero_add]`.
-/
theorem ev_top (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree ≤ s) : ev c (q * p) = p.coeff s * ev c (q * X ^ s) := by
  rw [ev_expand c q p (s + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ,
    Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero], zero_add]

/- English proof (translation)
Rewrite using `[mul_comm, ev_expand c _ q _ (Nat.lt_succ_self _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, ← monomial_one_right_eq_X_pow, ev_monomial, mul_one]`.
-/
theorem ev_X_pow_mul (m : ℕ) (q : F[X]) :
    ev c (q * X ^ m) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * c (m + j) := by
  rw [mul_comm, ev_expand c _ q _ (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_add, ← monomial_one_right_eq_X_pow, ev_monomial, mul_one]

/- English proof (translation)
Unfold `hankel at h`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Use `⟨∑ k : Fin (n + 1), monomial (k : ℕ) (v k), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Use `congrArg (fun p => Polynomial.coeff p k) h0` as an intermediate fact. Simplify `this` using `[Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Fin.val_inj]`. Conclude with `natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 k.2)`. Introduce `j hj`.

Use `congrFun hv ⟨j, Nat.lt_succ_of_le hj⟩` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this`. Rewrite using `[Finset.sum_mul, map_sum, ← this]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[monomial_mul_X_pow, ev_monomial, add_comm]`.
-/
theorem exists_kill (n : ℕ) (h : hankel c n = 0) :
    ∃ r : F[X], r ≠ 0 ∧ r.natDegree ≤ n ∧ ∀ j ≤ n, ev c (r * X ^ j) = 0 := by
  classical
  unfold hankel at h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨∑ k : Fin (n + 1), monomial (k : ℕ) (v k), ?_, ?_, ?_⟩
  · intro h0
    apply hv0
    funext k
    have := congrArg (fun p => Polynomial.coeff p k) h0
    simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Fin.val_inj] using this
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 k.2)
  · intro j hj
    have := congrFun hv ⟨j, Nat.lt_succ_of_le hj⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Finset.sum_mul, map_sum, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [monomial_mul_X_pow, ev_monomial, add_comm]

/- English proof (translation)
Establish `hex : ∃ d, ∃ q : F[X], q ≠ 0 ∧ q.natDegree = d ∧ d ≤ N ∧ ∀ j ≤ N, ev c (q * X ^ j) = 0`. Take `⟨r, hr0, hrd, hr⟩` from `exists_kill c N (hN N le_rfl)`. Conclude with `⟨_, r, hr0, rfl, hrd, hr⟩`. Take `⟨q0, hq00, hq0d, hdN, hq0⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ r : F[X], r ≠ 0 → r.natDegree < Nat.find hex → ¬ ∀ j ≤ N, ev c (r * X ^ j) = 0` using `fun r hr0 hrd hr => Nat.find_min hex hrd ⟨r, hr0, rfl, by omega, hr⟩`.

Establish `hlc : (q0.leadingCoeff)⁻¹ ≠ 0` using `inv_ne_zero (leadingCoeff_ne_zero.2 hq00)`. Choose the witnesses or unpack the hypotheses as in `⟨q, hqm, hqd, hqe⟩ : ∃ q : F[X], q.Monic ∧ q.natDegree = Nat.find hex ∧ ∀ j, ev c (q * X ^ j) = (q0.leadingCoeff)⁻¹ * ev c (q0 * X ^ j) := by`. Use `⟨q0 * C (q0.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq00, ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[natDegree_mul_C hlc, hq0d]`. Rewrite using `[show q0 * C (q0.leadingCoeff)⁻¹ * X ^ j = (q0.leadingCoeff)⁻¹ • (q0 * X ^ j) by`.

Rewrite using `[smul_eq_C_mul]`. Use the proof step `ring, map_smul, smul_eq_mul]`. Use `⟨q, hqm.ne_zero, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `hs : ev c (q * X ^ Nat.find hne) ≠ 0` using `Nat.find_spec hne`. Establish `hlt : ∀ j < Nat.find hne, ev c (q * X ^ j) = 0` using `fun j hj => by`. Assume the negation of the conclusion as `h`. Conclude with `Nat.find_min hne hj h`. Generalize the expression as in `Nat.find hne = s at hs hlt`.

Generalize the expression as in `Nat.find hex = d at hmin hqd hdN`. Establish `hNs : N < s`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hs` to reduce the goal to its premises.

Rewrite using `[hqe, hq0 s h, mul_zero]`. Take `⟨r, hr0, hrd, hr⟩` from `exists_kill c s (hN s hNs.le)`. Establish `hrk : ∀ p : F[X], p.natDegree ≤ s → ev c (r * p) = 0` using `fun p hp => by`. Rewrite using `[ev_top c r p s (fun j hj => hr j hj.le) hp, hr s le_rfl, mul_zero]`. Take `⟨r0, r1, hdiv, hr0deg⟩ : ∃ r0 r1 : F[X], r0 + q * r1 = r ∧ r0.degree < q.degree` from `⟨_, _, modByMonic_add_div r q, degree_modByMonic_lt r hqm⟩`.

Substitute `hdiv` using the available equality. Establish `hr0s : r0.natDegree < s`. Distinguish the cases in `hz : r0 = 0`. Rewrite using `[hz, natDegree_zero]`. Use linear arithmetic over natural numbers and integers.

Use `natDegree_lt_natDegree hz hr0deg` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h1 : r1 = 0`. Substitute `h1` using the available equality. Rewrite `hr0`, `hrd`, `hr` using `[mul_zero, add_zero]`.

Apply `hmin r0 hr0 (hqd ▸ natDegree_lt_natDegree hr0 hr0deg)` to reduce the goal to its premises. Introduce `j hj`. Conclude with `hr j (by omega)`. Establish `hdeg : d + r1.natDegree ≤ s`. Rewrite using `[← hqd, ← natDegree_mul hqm.ne_zero h1]`.

Establish `: q * r1 = r0 + q * r1 - r0` using `by ring`. Rewrite using `[this]`. Conclude with `(natDegree_sub_le _ _).trans (max_le hrd hr0s.le)`. Establish `key` using `hrk (q * X ^ (s - d - r1.natDegree)) (by rw [natDegree_mul_X_pow _ hqm.ne_zero, hqd]; omega)`. Rewrite `key` using `[add_mul, map_add]`.

Establish `h0 : ev c (r0 * (q * X ^ (s - d - r1.natDegree))) = 0`. Rewrite using `[show r0 * (q * X ^ (s - d - r1.natDegree)) = q * (r0 * X ^ (s - d - r1.natDegree)) by ring]`. Apply `ev_zero_of_lt c q _ s hlt` to reduce the goal to its premises. Distinguish the cases in `hz : r0 = 0`. Rewrite using `[hz, zero_mul, natDegree_zero]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[natDegree_mul_X_pow _ hz]`. Use `natDegree_lt_natDegree hz hr0deg` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hne1 : r1 * q ≠ 0` using `mul_ne_zero h1 hqm.ne_zero`.

Establish `hs' : s = (r1 * q).natDegree + (s - d - r1.natDegree)`. Rewrite using `[natDegree_mul h1 hqm.ne_zero, hqd]`. Use linear arithmetic over natural numbers and integers. Establish `hcoef : (r1 * q * X ^ (s - d - r1.natDegree)).coeff s = r1.leadingCoeff`. Use `coeff_mul_X_pow (r1 * q) (s - d - r1.natDegree) (r1 * q).natDegree` as an intermediate fact.

Rewrite `this` using `[← hs']`. Rewrite using `[this, coeff_natDegree, leadingCoeff_mul, hqm.leadingCoeff, mul_one]`. Establish `h2 : ev c (q * r1 * (q * X ^ (s - d - r1.natDegree))) = r1.leadingCoeff * ev c (q * X ^ s)`. Rewrite using `[show q * r1 * (q * X ^ (s - d - r1.natDegree)) = q * (r1 * q * X ^ (s - d - r1.natDegree)) by ring, ev_top c q _ s hlt (by rw [natDegree_mul_X_pow _ hne1]; omega), hcoef]`. Rewrite `key` using `[h0, h2, zero_add]`.

Conclude with `hs ((mul_eq_zero.1 key).resolve_left (leadingCoeff_ne_zero.2 h1))`.
-/
theorem exists_annihilator (N : ℕ) (hN : ∀ n, N ≤ n → hankel c n = 0) :
    ∃ q : F[X], q ≠ 0 ∧ ∀ j, ev c (q * X ^ j) = 0 := by
  classical
  have hex : ∃ d, ∃ q : F[X], q ≠ 0 ∧ q.natDegree = d ∧ d ≤ N ∧ ∀ j ≤ N, ev c (q * X ^ j) = 0 := by
    obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c N (hN N le_rfl)
    exact ⟨_, r, hr0, rfl, hrd, hr⟩
  obtain ⟨q0, hq00, hq0d, hdN, hq0⟩ := Nat.find_spec hex
  have hmin : ∀ r : F[X], r ≠ 0 → r.natDegree < Nat.find hex → ¬ ∀ j ≤ N, ev c (r * X ^ j) = 0 :=
    fun r hr0 hrd hr => Nat.find_min hex hrd ⟨r, hr0, rfl, by omega, hr⟩
  have hlc : (q0.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 hq00)
  obtain ⟨q, hqm, hqd, hqe⟩ : ∃ q : F[X], q.Monic ∧ q.natDegree = Nat.find hex ∧
      ∀ j, ev c (q * X ^ j) = (q0.leadingCoeff)⁻¹ * ev c (q0 * X ^ j) := by
    refine ⟨q0 * C (q0.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq00, ?_, fun j => ?_⟩
    · rw [natDegree_mul_C hlc, hq0d]
    · rw [show q0 * C (q0.leadingCoeff)⁻¹ * X ^ j = (q0.leadingCoeff)⁻¹ • (q0 * X ^ j) by
        rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]
  refine ⟨q, hqm.ne_zero, ?_⟩
  by_contra hne
  push_neg at hne
  have hs : ev c (q * X ^ Nat.find hne) ≠ 0 := Nat.find_spec hne
  have hlt : ∀ j < Nat.find hne, ev c (q * X ^ j) = 0 := fun j hj => by
    by_contra h; exact Nat.find_min hne hj h
  generalize Nat.find hne = s at hs hlt
  generalize Nat.find hex = d at hmin hqd hdN
  have hNs : N < s := by
    by_contra h
    push_neg at h
    apply hs
    rw [hqe, hq0 s h, mul_zero]
  obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c s (hN s hNs.le)
  have hrk : ∀ p : F[X], p.natDegree ≤ s → ev c (r * p) = 0 := fun p hp => by
    rw [ev_top c r p s (fun j hj => hr j hj.le) hp, hr s le_rfl, mul_zero]
  obtain ⟨r0, r1, hdiv, hr0deg⟩ : ∃ r0 r1 : F[X], r0 + q * r1 = r ∧ r0.degree < q.degree :=
    ⟨_, _, modByMonic_add_div r q, degree_modByMonic_lt r hqm⟩
  subst hdiv
  have hr0s : r0.natDegree < s := by
    by_cases hz : r0 = 0
    · rw [hz, natDegree_zero]; omega
    · have := natDegree_lt_natDegree hz hr0deg; omega
  by_cases h1 : r1 = 0
  · subst h1
    rw [mul_zero, add_zero] at hr0 hrd hr
    apply hmin r0 hr0 (hqd ▸ natDegree_lt_natDegree hr0 hr0deg)
    intro j hj
    exact hr j (by omega)
  · have hdeg : d + r1.natDegree ≤ s := by
      rw [← hqd, ← natDegree_mul hqm.ne_zero h1]
      have : q * r1 = r0 + q * r1 - r0 := by ring
      rw [this]
      exact (natDegree_sub_le _ _).trans (max_le hrd hr0s.le)
    have key := hrk (q * X ^ (s - d - r1.natDegree))
      (by rw [natDegree_mul_X_pow _ hqm.ne_zero, hqd]; omega)
    rw [add_mul, map_add] at key
    have h0 : ev c (r0 * (q * X ^ (s - d - r1.natDegree))) = 0 := by
      rw [show r0 * (q * X ^ (s - d - r1.natDegree)) = q * (r0 * X ^ (s - d - r1.natDegree)) by ring]
      apply ev_zero_of_lt c q _ s hlt
      by_cases hz : r0 = 0
      · rw [hz, zero_mul, natDegree_zero]; omega
      · rw [natDegree_mul_X_pow _ hz]
        have := natDegree_lt_natDegree hz hr0deg
        omega
    have hne1 : r1 * q ≠ 0 := mul_ne_zero h1 hqm.ne_zero
    have hs' : s = (r1 * q).natDegree + (s - d - r1.natDegree) := by
      rw [natDegree_mul h1 hqm.ne_zero, hqd]; omega
    have hcoef : (r1 * q * X ^ (s - d - r1.natDegree)).coeff s = r1.leadingCoeff := by
      have := coeff_mul_X_pow (r1 * q) (s - d - r1.natDegree) (r1 * q).natDegree
      rw [← hs'] at this
      rw [this, coeff_natDegree, leadingCoeff_mul, hqm.leadingCoeff, mul_one]
    have h2 : ev c (q * r1 * (q * X ^ (s - d - r1.natDegree))) = r1.leadingCoeff * ev c (q * X ^ s) := by
      rw [show q * r1 * (q * X ^ (s - d - r1.natDegree)) = q * (r1 * q * X ^ (s - d - r1.natDegree)) by ring,
        ev_top c q _ s hlt (by rw [natDegree_mul_X_pow _ hne1]; omega), hcoef]
    rw [h0, h2, zero_add] at key
    exact hs ((mul_eq_zero.1 key).resolve_left (leadingCoeff_ne_zero.2 h1))

/- English proof (translation)
Set `R : F[X]` to `∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k) * X ^ (q.natDegree - k)`. Use `⟨PowerSeries.trunc q.natDegree ((R : PowerSeries F) * φ), R, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg (fun p => Polynomial.coeff p 0) h0` as an intermediate fact. Simplify using `only [R, Polynomial.finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this`.

Rewrite `this` using `[Finset.sum_eq_single q.natDegree]`. Simplify using `only [Nat.sub_self, if_true] at this`. Conclude with `hq (leadingCoeff_eq_zero.1 this)`. Introduce `k hk hkd`. Use `Finset.mem_range.1 hk` as an intermediate fact.

Rewrite using `[if_neg (by omega)]`. Introduce `hk`. Conclude with `absurd (Finset.self_mem_range_succ _) hk`. Use extensionality with `n`. Rewrite using `[Polynomial.coeff_coe, PowerSeries.coeff_trunc]`.

Use `split_ifs with hn`. Both sides reduce to the same expression. Take `⟨m, rfl⟩ : ∃ m, n = m + q.natDegree` from `⟨n - q.natDegree, by omega⟩`. Establish `hR : (R : PowerSeries F) = ∑ k ∈ Finset.range (q.natDegree + 1), PowerSeries.C (q.coeff k) * PowerSeries.X ^ (q.natDegree - k)` using `by show Polynomial.coeToPowerSeries.ringHom R = _`. Rewrite using `[map_sum]`.

Simplify using `[Polynomial.coeToPowerSeries.ringHom_apply]`. Rewrite using `[hR, Finset.sum_mul, map_sum, ← h m, ev_X_pow_mul]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk'` using `Finset.mem_range.1 hk`. Rewrite using `[mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]`.

Rewrite using `[show m + q.natDegree - (q.natDegree - k) = m + k by omega]`.
-/
theorem isRat_of_ann (φ : PowerSeries F) (q : F[X]) (hq : q ≠ 0)
    (h : ∀ j, ev (fun i => PowerSeries.coeff i φ) (q * X ^ j) = 0) : IsRat φ := by
  classical
  let R : F[X] := ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k) * X ^ (q.natDegree - k)
  refine ⟨PowerSeries.trunc q.natDegree ((R : PowerSeries F) * φ), R, ?_, ?_⟩
  · intro h0
    have := congrArg (fun p => Polynomial.coeff p 0) h0
    simp only [R, Polynomial.finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single q.natDegree] at this
    · simp only [Nat.sub_self, if_true] at this
      exact hq (leadingCoeff_eq_zero.1 this)
    · intro k hk hkd
      have := Finset.mem_range.1 hk
      rw [if_neg (by omega)]
    · intro hk; exact absurd (Finset.self_mem_range_succ _) hk
  · ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + q.natDegree := ⟨n - q.natDegree, by omega⟩
      have hR : (R : PowerSeries F) = ∑ k ∈ Finset.range (q.natDegree + 1),
          PowerSeries.C (q.coeff k) * PowerSeries.X ^ (q.natDegree - k) := by
        show Polynomial.coeToPowerSeries.ringHom R = _
        rw [map_sum]
        simp [Polynomial.coeToPowerSeries.ringHom_apply]
      rw [hR, Finset.sum_mul, map_sum, ← h m, ev_X_pow_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
      rw [show m + q.natDegree - (q.natDegree - k) = m + k by omega]

end GlobalTheory.Nef.Kron

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `F _ φ N hN`. Take `⟨q, hq, h⟩` from `Kron.exists_annihilator _ N hN`. Conclude with `Kron.isRat_of_ann φ q hq h`.
-/
theorem isRat_of_hankel_eventually_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ),
    (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  intro F _ φ N hN
  obtain ⟨q, hq, h⟩ := Kron.exists_annihilator _ N hN
  exact Kron.isRat_of_ann φ q hq h

end GlobalTheory.Nef
