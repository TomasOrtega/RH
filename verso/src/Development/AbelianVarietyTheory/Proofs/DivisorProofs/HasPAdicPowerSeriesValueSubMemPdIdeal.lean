import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.HasValCong

open scoped Nat

section Ring

variable {B : Type} [CommRing B]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn x hx`. Distinguish the cases in `hpn : p ∣ n`.

Take `⟨m, rfl⟩` from `hpn`. Establish `hm : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hn)`. Establish `hmn : m < p * m`. Use `hp.two_le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨y, hy, hxy⟩` from `hJ x hx`. Take `⟨y', hy', hyy⟩` from `ih m hmn hm y hy`. Use `⟨y', hy', ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.factorization_factorial_mul hp, pow_mul, hxy, mul_pow, hyy, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Conclude with `⟨x, hx, by simp⟩`. Take `⟨y, hy, hxy⟩` from `ih k (by omega) hk x hx`. Use `⟨x * y, J.mul_mem_left x hy, ?_⟩` and prove the remaining obligations.

Establish `h0 : (k + 1).factorization p = 0` using `Nat.factorization_eq_zero_of_not_dvd hpn`. Rewrite using `[Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero k), Finsupp.coe_add, Pi.add_apply, h0, zero_add, pow_succ, hxy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_eq_pow_factorization_mul (p : ℕ) (hp : p.Prime) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ x ∈ J, ∃ y ∈ J, x ^ n = (p : B) ^ ((n)!.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmn : m < p * m := by
        have := hp.two_le
        nlinarith
      obtain ⟨y, hy, hxy⟩ := hJ x hx
      obtain ⟨y', hy', hyy⟩ := ih m hmn hm y hy
      refine ⟨y', hy', ?_⟩
      rw [Nat.factorization_factorial_mul hp, pow_mul, hxy, mul_pow, hyy, pow_add]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨x, hx, by simp⟩
      obtain ⟨y, hy, hxy⟩ := ih k (by omega) hk x hx
      refine ⟨x * y, J.mul_mem_left x hy, ?_⟩
      have h0 : (k + 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero k),
        Finsupp.coe_add, Pi.add_apply, h0, zero_add, pow_succ, hxy]
      ring

/- English proof (translation)
Take `⟨y, hy, hxy⟩` from `pow_eq_pow_factorization_mul p hp J hJ n hn x hx`. Take `⟨u, hu'⟩` from `hu (n ! / p ^ (n !).factorization p) (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm`. Use `⟨(↑u⁻¹ : B) * y, J.mul_mem_left _ hy, ?_⟩` and prove the remaining obligations. Establish `hfac : ((n ! : ℕ) : B) = (p : B) ^ (n !).factorization p * ((n ! / p ^ (n !).factorization p : ℕ) : B)`. Rewrite using `[← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]`.

Rewrite using `[hxy, hfac, ← hu', mul_assoc, ← mul_assoc (u : B), Units.mul_inv, one_mul]`.
-/
theorem pow_eq_factorial_mul (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (n : ℕ) (hn : 0 < n) (x : B) (hx : x ∈ J) :
    ∃ y ∈ J, x ^ n = ((n ! : ℕ) : B) * y := by
  obtain ⟨y, hy, hxy⟩ := pow_eq_pow_factorization_mul p hp J hJ n hn x hx
  obtain ⟨u, hu'⟩ := hu (n ! / p ^ (n !).factorization p)
    (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  refine ⟨(↑u⁻¹ : B) * y, J.mul_mem_left _ hy, ?_⟩
  have hfac : ((n ! : ℕ) : B) =
      (p : B) ^ (n !).factorization p * ((n ! / p ^ (n !).factorization p : ℕ) : B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hxy, hfac, ← hu', mul_assoc, ← mul_assoc (u : B), Units.mul_inv, one_mul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, J.zero_mem, by simp⟩`. Consider the case `insert i s hi ih`. Take `⟨y, hy, e⟩` from `h i (Finset.mem_insert_self i s)`. Take `⟨y', hy', e'⟩` from `ih (fun k hk => h k (Finset.mem_insert_of_mem hk))`.

Conclude with `⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', mul_add]⟩`.
-/
theorem sum_eq_mul_mem {ι : Type} (s : Finset ι) (c : B) (J : Ideal B) (f : ι → B)
    (h : ∀ i ∈ s, ∃ y ∈ J, f i = c * y) : ∃ y ∈ J, ∑ i ∈ s, f i = c * y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', mul_add]⟩

/- English proof (translation)
Break down `n with _ | n` into its components or cases. Conclude with `⟨0, J.zero_mem, by simp⟩`. Rewrite using `[add_comm a j, add_pow, Finset.sum_range_succ']`. Simplify using `only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]`. Rewrite using `[add_sub_cancel_right]`.

Apply `sum_eq_mul_mem` to reduce the goal to its premises. Introduce `k _`. Take `⟨y, hy, hjy⟩` from `pow_eq_factorial_mul p hp hu J hJ (k + 1) (Nat.succ_pos k) j hj`. Use `⟨((n.descFactorial k : ℕ) : B) * a ^ (n + 1 - (k + 1)) * y, J.mul_mem_left _ hy, ?_⟩` and prove the remaining obligations. Establish `h : (n + 1).choose (k + 1) * (k + 1)! = (n + 1) * n.descFactorial k`.

Rewrite using `[mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ]`. Establish `h' : (((n + 1).choose (k + 1) : ℕ) : B) * (((k + 1)! : ℕ) : B) = ((n + 1 : ℕ) : B) * ((n.descFactorial k : ℕ) : B)`. Rewrite using `[← Nat.cast_mul, ← Nat.cast_mul, h]`. Rewrite using `[hjy]`. Take the linear combination `(a ^ (n + 1 - (k + 1)) * y) * h'`.
-/
theorem add_pow_sub_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (a j : B) (hj : j ∈ J) (n : ℕ) :
    ∃ y ∈ J, (a + j) ^ n - a ^ n = (n : B) * y := by
  rcases n with _ | n
  · exact ⟨0, J.zero_mem, by simp⟩
  rw [add_comm a j, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
  rw [add_sub_cancel_right]
  apply sum_eq_mul_mem
  intro k _
  obtain ⟨y, hy, hjy⟩ := pow_eq_factorial_mul p hp hu J hJ (k + 1) (Nat.succ_pos k) j hj
  refine ⟨((n.descFactorial k : ℕ) : B) * a ^ (n + 1 - (k + 1)) * y, J.mul_mem_left _ hy, ?_⟩
  have h : (n + 1).choose (k + 1) * (k + 1)! = (n + 1) * n.descFactorial k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ]
  have h' : (((n + 1).choose (k + 1) : ℕ) : B) * (((k + 1)! : ℕ) : B) =
      ((n + 1 : ℕ) : B) * ((n.descFactorial k : ℕ) : B) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, h]
  rw [hjy]
  linear_combination (a ^ (n + 1 - (k + 1)) * y) * h'

end Ring

section Monomial

variable {B : Type} [CommRing B] {σ : Type}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, fun _ => J.zero_mem, by simp⟩`. Consider the case `insert i s hi ih`. Take `⟨b, hb, e⟩` from `ih`. Take `⟨y, hy, ey⟩` from `add_pow_sub_pow p hp hu J hJ (z' i) (z i - z' i) (hz i) (α i)`.

Establish `hzz : z' i + (z i - z' i) = z i` using `by ring`. Rewrite `ey` using `[hzz]`. Use `⟨Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k), ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `J.mul_mem_right _ hy`. Rewrite using `[Function.update_of_ne hk]`. Conclude with `J.mul_mem_left _ (hb k)`.

Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Function.update_self]`. Establish `h1 : ∑ k ∈ s, (α k : B) * Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k) k = z' i ^ α i * ∑ k ∈ s, (α k : B) * b k`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (by rintro rfl; exact hi hk)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Take the linear combination `(∏ k ∈ s, z k ^ α k) * ey + z' i ^ α i * e`.
-/
theorem prod_pow_sub_prod_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ → ℕ) (s : Finset σ) :
    ∃ b : σ → B, (∀ i, b i ∈ J) ∧
      ∏ i ∈ s, z i ^ α i - ∏ i ∈ s, z' i ^ α i = ∑ i ∈ s, (α i : B) * b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b, hb, e⟩ := ih
    obtain ⟨y, hy, ey⟩ := add_pow_sub_pow p hp hu J hJ (z' i) (z i - z' i) (hz i) (α i)
    have hzz : z' i + (z i - z' i) = z i := by ring
    rw [hzz] at ey
    refine ⟨Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k), ?_, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact J.mul_mem_right _ hy
      · rw [Function.update_of_ne hk]
        exact J.mul_mem_left _ (hb k)
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Function.update_self]
      have h1 : ∑ k ∈ s, (α k : B) *
          Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k) k =
          z' i ^ α i * ∑ k ∈ s, (α k : B) * b k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
        ring
      rw [h1]
      linear_combination (∏ k ∈ s, z k ^ α k) * ey + z' i ^ α i * e

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, J.zero_mem, by simp⟩`. Consider the case `insert i s hi ih`. Take `⟨y, hy, e⟩` from `h i (Finset.mem_insert_self i s)`. Take `⟨y', hy', e'⟩` from `ih (fun k hk => h k (Finset.mem_insert_of_mem hk))`.

Conclude with `⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', map_add]⟩`.
-/
theorem sum_eq_map_mem {Q : Type} [CommRing Q] [Algebra B Q] {ι : Type} (s : Finset ι)
    (J : Ideal B) (f : ι → Q) (h : ∀ i ∈ s, ∃ b ∈ J, f i = algebraMap B Q b) :
    ∃ b ∈ J, ∑ i ∈ s, f i = algebraMap B Q b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', map_add]⟩

variable [Fintype σ] {Q : Type} [CommRing Q] [Algebra B Q]

/- English proof (translation)
Use `choose c hc using ha`. Take `⟨b, hb, e⟩` from `prod_pow_sub_prod_pow p hp hu J hJ z z' hz α Finset.univ`. Use `⟨∑ i, b i * c i, J.sum_mem (fun i _ => J.mul_mem_right _ (hb i)), ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg (algebraMap B Q) e`. Simplify using `only [map_sub, map_prod, map_pow, map_sum, map_mul, map_natCast] at e'`.

Rewrite using `[← mul_sub, e', Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hc i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem monomial_val_sub (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ →₀ ℕ) (a : Q) (ha : ∀ i, ∃ c : B, (α i : Q) * a = algebraMap B Q c) :
    ∃ b ∈ J, a * (∏ i, algebraMap B Q (z i) ^ α i) - a * ∏ i, algebraMap B Q (z' i) ^ α i =
      algebraMap B Q b := by
  choose c hc using ha
  obtain ⟨b, hb, e⟩ := prod_pow_sub_prod_pow p hp hu J hJ z z' hz α Finset.univ
  refine ⟨∑ i, b i * c i, J.sum_mem (fun i _ => J.mul_mem_right _ (hb i)), ?_⟩
  have e' := congrArg (algebraMap B Q) e
  simp only [map_sub, map_prod, map_pow, map_sum, map_mul, map_natCast] at e'
  rw [← mul_sub, e', Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hc i]
  ring

/- English proof (translation)
Rewrite using `[P.as_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]`. Apply `sum_eq_map_mem` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Conclude with `monomial_val_sub p hp hu J hJ z z' hz v (P.coeff v) (hP v)`.
-/
theorem eval_sub_eval (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (P : MvPolynomial σ Q)
    (hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) * P.coeff α = algebraMap B Q c) :
    ∃ b ∈ J, MvPolynomial.eval (fun i => algebraMap B Q (z i)) P -
      MvPolynomial.eval (fun i => algebraMap B Q (z' i)) P = algebraMap B Q b := by
  rw [P.as_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply sum_eq_map_mem
  intro v _
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact monomial_val_sub p hp hu J hJ z z' hz v (P.coeff v) (hP v)

end Monomial

/- English proof (translation)
Introduce `p hpf B O Q _ _ _ _ θ hF σ _ _ z _ J hJ z' f q q' hzz hD hv hv' m`. Establish `hp : p.Prime` using `hpf.out`. Take `⟨N1, h1⟩` from `hv m`. Take `⟨N2, h2⟩` from `hv' m`. Take `⟨b1, e1⟩` from `h1 (max N1 N2) (le_max_left _ _)`.

Take `⟨b2, e2⟩` from `h2 (max N1 N2) (le_max_right _ _)`. Establish `hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) * (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max N1 N2) f).coeff α = algebraMap B Q c`. Introduce `α i`. Rewrite using `[coeff_trunc']`. Use `split_ifs`.

Take `⟨c, -, hc⟩` from `hD α i`. Conclude with `⟨c, hc⟩`. Conclude with `⟨0, by simp⟩`. Take `⟨b, hb, e⟩` from `eval_sub_eval p hp hF.unit_coprime J hJ z z' hzz _ hP`. Use `⟨b, hb, b1 - b2, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_sub, map_pow, map_natCast] at e1 e2 ⊢`. Take the linear combination `e1 - e2 + e`.
-/
theorem hasVal_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q),
    (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' →
    ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  intro p hpf B O Q _ _ _ _ θ hF σ _ _ z _ J hJ z' f q q' hzz hD hv hv' m
  have hp : p.Prime := hpf.out
  obtain ⟨N1, h1⟩ := hv m
  obtain ⟨N2, h2⟩ := hv' m
  obtain ⟨b1, e1⟩ := h1 (max N1 N2) (le_max_left _ _)
  obtain ⟨b2, e2⟩ := h2 (max N1 N2) (le_max_right _ _)
  have hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) *
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max N1 N2) f).coeff α =
        algebraMap B Q c := by
    intro α i
    rw [coeff_trunc']
    split_ifs
    · obtain ⟨c, -, hc⟩ := hD α i
      exact ⟨c, hc⟩
    · exact ⟨0, by simp⟩
  obtain ⟨b, hb, e⟩ := eval_sub_eval p hp hF.unit_coprime J hJ z z' hzz _ hP
  refine ⟨b, hb, b1 - b2, ?_⟩
  simp only [map_add, map_mul, map_sub, map_pow, map_natCast] at e1 e2 ⊢
  linear_combination e1 - e2 + e

end GlobalTheory.HasValCong
