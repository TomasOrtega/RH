import Mathlib

open scoped PowerSeries Pointwise

namespace GlobalTheory

namespace WittIntegrality

open WittVector

variable {C : Type} [Field C] (A : ValuationSubring C)

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Break down `A.mem_or_inv_mem c with hc | hc` into its components or cases. Conclude with `hc`. Distinguish the cases in `h0 : c = 0`. Rewrite using `[h0]`.

Conclude with `A.zero_mem`. Establish `e : c = c ^ (m + 1) * c⁻¹ ^ m`. Rewrite using `[pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, mul_one]`. Rewrite using `[e]`. Conclude with `mul_mem h (pow_mem hc _)`.
-/
lemma mem_of_pow_mem {c : C} {k : ℕ} (hk : 1 ≤ k) (h : c ^ k ∈ A) : c ∈ A := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases A.mem_or_inv_mem c with hc | hc
  · exact hc
  · by_cases h0 : c = 0
    · rw [h0]; exact A.zero_mem
    · have e : c = c ^ (m + 1) * c⁻¹ ^ m := by
        rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, mul_one]
      rw [e]; exact mul_mem h (pow_mem hc _)

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def S : Subring (WittVector p C) := (WittVector.map (p := p) A.subtype).range

variable {p}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ k`. Rewrite using `[WittVector.map_coeff]`. Conclude with `(y.coeff k).2`. Introduce `h`.

Use `⟨WittVector.mk p fun k => ⟨x.coeff k, h k⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Rewrite using `[WittVector.map_coeff]`. Both sides reduce to the same expression.
-/
lemma mem_S (x : WittVector p C) : x ∈ S A p ↔ ∀ k, x.coeff k ∈ A := by
  constructor
  · rintro ⟨y, rfl⟩ k
    rw [WittVector.map_coeff]
    exact (y.coeff k).2
  · intro h
    refine ⟨WittVector.mk p fun k => ⟨x.coeff k, h k⟩, ?_⟩
    ext k
    rw [WittVector.map_coeff]
    rfl

/- English proof (translation)
Rewrite using `[mem_S]`. Introduce `k`. Consider the cases of `k with`. Consider the case `zero => rwa [teichmuller_coeff_zero]`. Consider the case `succ k => rw [teichmuller_coeff_pos p c _ (Nat.succ_pos k)]`.

Conclude with `A.zero_mem`.
-/
lemma teich_mem {c : C} (hc : c ∈ A) : teichmuller p c ∈ S A p := by
  rw [mem_S]
  intro k
  cases k with
  | zero => rwa [teichmuller_coeff_zero]
  | succ k => rw [teichmuller_coeff_pos p c _ (Nat.succ_pos k)]; exact A.zero_mem

variable [CharP C p]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_S]`. Introduce `k`. Rewrite using `[coeff_frobenius_charP]`. Conclude with `pow_mem (hx k) _`.
-/
lemma frob_mem {x : WittVector p C} (hx : x ∈ S A p) : frobenius x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  rw [coeff_frobenius_charP]
  exact pow_mem (hx k) _

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_S]`. Introduce `k`. Use `hx (k + 1)` as an intermediate fact. Rewrite `this` using `[mul_charP_coeff_succ]`. Conclude with `mem_of_pow_mem A hp.out.one_lt.le this`.
-/
lemma mem_of_mul_p_mem {x : WittVector p C} (hx : x * (p : WittVector p C) ∈ S A p) :
    x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  have := hx (k + 1)
  rw [mul_charP_coeff_succ] at this
  exact mem_of_pow_mem A hp.out.one_lt.le this

variable [PerfectRing C p]

noncomputable def tail (x : WittVector p C) : WittVector p C :=
  WittVector.mk p fun k => (frobeniusEquiv C p).symm (x.coeff (k + 1))

/- English proof (translation)
Simplify using `only [tail, WittVector.coeff_mk, frobeniusEquiv_symm_pow_p]`.
-/
lemma tail_coeff (x : WittVector p C) (k : ℕ) : x.coeff (k + 1) = (tail x).coeff k ^ p := by
  simp only [tail, WittVector.coeff_mk, frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[coeff_add_of_disjoint]`. Consider the cases of `k with`. Consider the case `zero => rw [teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]`. Consider the case `succ k`.

Rewrite using `[teichmuller_coeff_pos p _ _ (Nat.succ_pos k), mul_charP_coeff_succ, zero_add, tail_coeff]`. Introduce `k`. Consider the cases of `k with`. Consider the case `zero => exact Or.inr (mul_charP_coeff_zero _)`. Consider the case `succ k => exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos k))`.
-/
lemma decomp (x : WittVector p C) : x = teichmuller p (x.coeff 0) + tail x * p := by
  ext k
  rw [coeff_add_of_disjoint]
  · cases k with
    | zero => rw [teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]
    | succ k =>
      rw [teichmuller_coeff_pos p _ _ (Nat.succ_pos k), mul_charP_coeff_succ, zero_add, tail_coeff]
  · intro k
    cases k with
    | zero => exact Or.inr (mul_charP_coeff_zero _)
    | succ k => exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos k))

/- English proof (translation)
Establish `he : ∀ i j, (Z i j).coeff 0 ^ p = ∑ a, (Y i a).coeff 0 * (Z a j).coeff 0 + (B i j).coeff 0`. Introduce `i j`. Use `congrArg (WittVector.constantCoeff (p := p) (R := C)) (h i j)` as an intermediate fact. Simplify using `only [map_add, map_sum, map_mul, WittVector.constantCoeff_apply, coeff_frobenius_charP] at this`. Conclude with `this`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨i0, j0, hij⟩` from `hne`. Take `⟨⟨i1, j1⟩, -, hmax⟩` from `Finset.exists_max_image (Finset.univ : Finset (n × n)) (fun q => A.valuation ((Z q.1 q.2).coeff 0)) ⟨(i0, j0), Finset.mem_univ _⟩`. Use `set z1 := (Z i1 j1).coeff 0 with hz1`.

Establish `h1 : 1 < A.valuation z1`. Establish `a` using `hmax (i0, j0) (Finset.mem_univ _)`. Establish `b : ¬ A.valuation ((Z i0 j0).coeff 0) ≤ 1` using `by rwa [A.valuation_le_one_iff]`. Conclude with `lt_of_lt_of_le (not_le.mp b) a`. Establish `hz1A : z1 ∉ A`.

Rewrite using `[← A.valuation_le_one_iff]`. Conclude with `not_le.mpr h1`. Establish `hz0 : z1 ≠ 0` using `fun e => hz1A (e ▸ A.zero_mem)`. Establish `hle : A.valuation (z1 ^ p) ≤ A.valuation z1`. Rewrite using `[hz1, he i1 j1]`.

Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations. Use `Valuation.map_sum_le _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `((A.valuation_le_one_iff _).2 ((mem_S A _).1 (hB i1 j1) 0)).trans h1.le`.

Establish `hpm : z1 ^ (p - 1) ∈ A`. Rewrite using `[← A.valuation_le_one_iff]`. Establish `e : z1 ^ (p - 1) = z1 ^ p * z1⁻¹`. Take `⟨m, hm⟩ : ∃ m, p = m + 1` from `⟨p - 1, by have := hp.out.one_lt; omega⟩`. Rewrite using `[hm, Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hz0, mul_one]`.

Rewrite using `[e, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hz1A (mem_of_pow_mem A (by have := hp.out.two_le; omega) hpm)`.
-/
lemma key0 {n : Type} [Fintype n] (Y Z B : Matrix n n (WittVector p C))
    (hY : ∀ i j, Y i j ∈ S A p) (hB : ∀ i j, B i j ∈ S A p)
    (h : ∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) :
    ∀ i j, (Z i j).coeff 0 ∈ A := by
  classical
  have he : ∀ i j, (Z i j).coeff 0 ^ p =
      ∑ a, (Y i a).coeff 0 * (Z a j).coeff 0 + (B i j).coeff 0 := by
    intro i j
    have := congrArg (WittVector.constantCoeff (p := p) (R := C)) (h i j)
    simp only [map_add, map_sum, map_mul, WittVector.constantCoeff_apply,
      coeff_frobenius_charP] at this
    exact this
  by_contra hne
  push_neg at hne
  obtain ⟨i0, j0, hij⟩ := hne
  obtain ⟨⟨i1, j1⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n))
    (fun q => A.valuation ((Z q.1 q.2).coeff 0)) ⟨(i0, j0), Finset.mem_univ _⟩
  set z1 := (Z i1 j1).coeff 0 with hz1
  have h1 : 1 < A.valuation z1 := by
    have a := hmax (i0, j0) (Finset.mem_univ _)
    have b : ¬ A.valuation ((Z i0 j0).coeff 0) ≤ 1 := by rwa [A.valuation_le_one_iff]
    exact lt_of_lt_of_le (not_le.mp b) a
  have hz1A : z1 ∉ A := by
    rw [← A.valuation_le_one_iff]; exact not_le.mpr h1
  have hz0 : z1 ≠ 0 := fun e => hz1A (e ▸ A.zero_mem)
  have hle : A.valuation (z1 ^ p) ≤ A.valuation z1 := by
    rw [hz1, he i1 j1]
    refine Valuation.map_add_le _ ?_ ?_
    · refine Valuation.map_sum_le _ fun a _ => ?_
      rw [map_mul]
      calc A.valuation ((Y i1 a).coeff 0) * A.valuation ((Z a j1).coeff 0)
          ≤ 1 * A.valuation ((Z a j1).coeff 0) :=
            by gcongr; exact (A.valuation_le_one_iff _).2 ((mem_S A _).1 (hY i1 a) 0)
        _ ≤ A.valuation z1 := by rw [one_mul]; exact hmax (a, j1) (Finset.mem_univ _)
    · exact ((A.valuation_le_one_iff _).2 ((mem_S A _).1 (hB i1 j1) 0)).trans h1.le
  have hpm : z1 ^ (p - 1) ∈ A := by
    rw [← A.valuation_le_one_iff]
    have e : z1 ^ (p - 1) = z1 ^ p * z1⁻¹ := by
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [e, map_mul]
    calc A.valuation (z1 ^ p) * A.valuation z1⁻¹ ≤ A.valuation z1 * A.valuation z1⁻¹ :=
          by gcongr
      _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
  exact hz1A (mem_of_pow_mem A (by have := hp.out.two_le; omega) hpm)

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact fun Z B hB h => key0 A Y Z B hY hB h`. Consider the case `succ k ih`. Introduce `Z B hB h`.

Establish `h0` using `key0 A Y Z B hY hB h`. Set `U : Matrix n n (WittVector p C)` to `fun i j => tail (Z i j)`. Set `D : Matrix n n (WittVector p C)` to `fun i j => frobenius (U i j) - ∑ a, Y i a * U a j`. Establish `hD : ∀ i j, D i j * p = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0) + B i j - frobenius (teichmuller p ((Z i j).coeff 0))`. Introduce `i j`.

Establish `e1 : frobenius (Z i j) = frobenius (teichmuller p ((Z i j).coeff 0)) + frobenius (U i j) * p` using `by conv_lhs => rw [decomp (Z i j)]`. Rewrite using `[map_add, map_mul, map_natCast]`. Establish `e2 : ∑ a, Y i a * Z a j = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0) + (∑ a, Y i a * U a j) * p`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `conv_lhs => rw [decomp (Z a j)]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4` using `h i j`. Rewrite `e4` using `[e1, e2]`. Simplify using `only [D]`.

Take the linear combination `e4`. Establish `hDm : ∀ i j, D i j ∈ S A p`. Introduce `i j`. Use `mem_of_mul_p_mem A ?_` and prove the remaining obligations. Rewrite using `[hD]`.

Conclude with `Subring.sub_mem _ (Subring.add_mem _ (Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hY i a) (teich_mem A (h0 a j))) (hB i j)) (frob_mem A (teich_mem A (h0 i j)))`. Establish `hU` using `ih U D hDm (fun i j => by simp only [D]; ring)`. Introduce `i j`. Rewrite using `[tail_coeff]`. Conclude with `pow_mem (hU i j) _`.
-/
lemma key {n : Type} [Fintype n] (Y : Matrix n n (WittVector p C)) (hY : ∀ i j, Y i j ∈ S A p) :
    ∀ (k : ℕ) (Z B : Matrix n n (WittVector p C)), (∀ i j, B i j ∈ S A p) →
    (∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) →
    ∀ i j, (Z i j).coeff k ∈ A := by
  intro k
  induction k with
  | zero => exact fun Z B hB h => key0 A Y Z B hY hB h
  | succ k ih =>
    intro Z B hB h
    have h0 := key0 A Y Z B hY hB h
    let U : Matrix n n (WittVector p C) := fun i j => tail (Z i j)
    let D : Matrix n n (WittVector p C) :=
      fun i j => frobenius (U i j) - ∑ a, Y i a * U a j
    have hD : ∀ i j, D i j * p = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0) + B i j
        - frobenius (teichmuller p ((Z i j).coeff 0)) := by
      intro i j
      have e1 : frobenius (Z i j) = frobenius (teichmuller p ((Z i j).coeff 0))
          + frobenius (U i j) * p := by
        conv_lhs => rw [decomp (Z i j)]
        rw [map_add, map_mul, map_natCast]
      have e2 : ∑ a, Y i a * Z a j = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0)
          + (∑ a, Y i a * U a j) * p := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [decomp (Z a j)]
        ring
      have e4 := h i j
      rw [e1, e2] at e4
      simp only [D]
      linear_combination e4
    have hDm : ∀ i j, D i j ∈ S A p := by
      intro i j
      refine mem_of_mul_p_mem A ?_
      rw [hD]
      exact Subring.sub_mem _ (Subring.add_mem _ (Subring.sum_mem _ fun a _ =>
        Subring.mul_mem _ (hY i a) (teich_mem A (h0 a j))) (hB i j))
        (frob_mem A (teich_mem A (h0 i j)))
    have hU := ih U D hDm (fun i j => by simp only [D]; ring)
    intro i j
    rw [tail_coeff]
    exact pow_mem (hU i j) _

end WittIntegrality

open WittIntegrality in
/- English proof (translation)
Introduce `p _ C _ _ _ A n _ Z Y h i j m`. Break down `h with h | h` into its components or cases. Use `key A (Y.map (WittVector.map A.subtype)) (fun i j => ⟨Y i j, rfl⟩) m Z 0 (fun _ _ => Subring.zero_mem _) ?_ i j` and prove the remaining obligations. Introduce `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.map_apply, Matrix.mul_apply]`. Rewrite using `[this, Matrix.zero_apply, add_zero]`. Use `key A (Y.map (WittVector.map A.subtype)).transpose (fun i j => ⟨Y j i, rfl⟩) m Z.transpose 0 (fun _ _ => Subring.zero_mem _) ?_ j i` and prove the remaining obligations. Introduce `i j`. Use `congrFun (congrFun h j) i` as an intermediate fact.

Rewrite `this` using `[Matrix.map_apply, Matrix.mul_apply]`. Rewrite using `[Matrix.transpose_apply, this, Matrix.zero_apply, add_zero]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.
-/
theorem witt_matrix_coeff_mem_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [CharP C p] [PerfectRing C p] (A : ValuationSubring C) {n : Type} [Fintype n] (Z : Matrix n n (WittVector p C)) (Y : Matrix n n (WittVector p A)), (Z.map WittVector.frobenius = Y.map (WittVector.map A.subtype) * Z ∨ Z.map WittVector.frobenius = Z * Y.map (WittVector.map A.subtype)) → ∀ i j m, (Z i j).coeff m ∈ A := by
  intro p _ C _ _ _ A n _ Z Y h i j m
  rcases h with h | h
  · refine key A (Y.map (WittVector.map A.subtype)) (fun i j => ⟨Y i j, rfl⟩) m Z 0
      (fun _ _ => Subring.zero_mem _) ?_ i j
    intro i j
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this, Matrix.zero_apply, add_zero]
  · refine key A (Y.map (WittVector.map A.subtype)).transpose (fun i j => ⟨Y j i, rfl⟩) m
      Z.transpose 0 (fun _ _ => Subring.zero_mem _) ?_ j i
    intro i j
    have := congrFun (congrFun h j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [Matrix.transpose_apply, this, Matrix.zero_apply, add_zero]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end GlobalTheory
