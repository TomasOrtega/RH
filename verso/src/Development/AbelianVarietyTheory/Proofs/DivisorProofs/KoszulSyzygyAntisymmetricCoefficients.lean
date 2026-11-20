import Mathlib

open MvPolynomial Finset

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ r G hG`. Set `R : ℕ → MvPolynomial (Fin r) A →ₐ[A] MvPolynomial (Fin r) A` to `fun n => aeval (fun j : Fin r => if (j : ℕ) < n then 0 else X j)`. Establish `hRX : ∀ n (k : Fin r), R n (X k) = if (k : ℕ) < n then 0 else X k`. Introduce `n k`. Simplify using `[R]`.

Establish `hR0 : ∀ P, R 0 P = P`. Introduce `P`. Establish `: (fun j : Fin r => if (j : ℕ) < 0 then (0 : MvPolynomial (Fin r) A) else X j) = X`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Simplify using `only [R, this, aeval_X_left_apply]`. Establish `hdvd : ∀ (i : Fin r) (P : MvPolynomial (Fin r) A), X i ∣ R i P - R (i + 1) P`. Introduce `i P`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [R]`.

Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `dvd_add hp hq`. Consider the case `mul_X p k hp`. Rewrite using `[map_mul, map_mul]`.

Establish `e : R i p * R i (X k) - R (i + 1) p * R (i + 1) (X k) = R i p * (R i (X k) - R (i + 1) (X k)) + (R i p - R (i + 1) p) * R (i + 1) (X k)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `dvd_add (dvd_mul_of_dvd_right ?_ _) (dvd_mul_of_dvd_left hp _)` and prove the remaining obligations. Rewrite using `[hRX, hRX]`.

Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Simplify using the standard rewrite rules. Establish `: (k : ℕ) ≠ i` using `fun h => hki (Fin.ext h)`. Distinguish the cases in `hk : (k : ℕ) < i`.

Simplify using `[hk, show (k : ℕ) < i + 1 by omega]`. Simplify using `[hk, show ¬ (k : ℕ) < i + 1 by omega]`. Use `choose D hD using hdvd`. Establish `htel : ∀ (P : MvPolynomial (Fin r) A) (n : ℕ), n ≤ r → P - R n P = ∑ j : Fin r, if (j : ℕ) < n then X j * D j P else 0`. Introduce `P n`.

Proceed by induction on `n with`. Consider the case `zero => intro _`. Simplify using `[hR0]`. Consider the case `succ n ih`. Introduce `hn`.

Establish `hlt : n < r` using `by omega`. Establish `pt : ∀ j : Fin r, (if (j : ℕ) < n + 1 then X j * D j P else 0) = (if (j : ℕ) < n then X j * D j P else 0) + (if j = ⟨n, hlt⟩ then X j * D j P else 0)`. Introduce `j`. Distinguish the cases in `h1 : (j : ℕ) < n`. Establish `: j ≠ ⟨n, hlt⟩` using `fun h => by subst h; simp at h1`.

Simplify using `[h1, this, show (j : ℕ) < n + 1 by omega]`. Distinguish the cases in `h2 : (j : ℕ) = n`. Establish `: j = ⟨n, hlt⟩` using `Fin.ext h2`. Simplify using `[h1, this]`. Establish `: j ≠ ⟨n, hlt⟩` using `fun h => h2 (by rw [h])`.

Simplify using `[h1, this, show ¬ (j : ℕ) < n + 1 by omega]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => pt j), Finset.sum_add_distrib, ← ih (by omega), Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _), ← hD]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrel : ∀ n, ∑ j : Fin r, (if (j : ℕ) < n then 0 else X j) * R n (G j) = 0`. Introduce `n`.

Use `congrArg (R n) hG` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify `this` using `[map_mul, hRX]`. Establish `key : ∀ i : Fin r, R i (G i) + ∑ j : Fin r, (if i < j then X j * D i (G j) else 0) = 0`. Introduce `i`.

Establish `h1` using `hrel i`. Establish `h2` using `hrel (i + 1)`. Establish `s1 : ∀ j : Fin r, (if (j : ℕ) < i then 0 else X j) * R i (G j) = (if j = i then X i * R i (G i) else 0) + (if i < j then X j * R i (G j) else 0)`. Introduce `j`. Break down `lt_trichotomy j i with h | h | h` into its components or cases.

Establish `: (j : ℕ) < i` using `h`. Simplify using `[this, h.ne, not_lt.mpr h.le]`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `: ¬ (j : ℕ) < i` using `by have : (i : ℕ) < j := h; omega`.

Simplify using `[this, h.ne', h]`. Establish `s2 : ∀ j : Fin r, (if (j : ℕ) < i + 1 then 0 else X j) * R (i + 1) (G j) = (if i < j then X j * R (i + 1) (G j) else 0)`. Introduce `j`. Distinguish the cases in `h : i < j`. Establish `: ¬ (j : ℕ) < i + 1` using `by have : (i : ℕ) < j := h; omega`.

Simplify using `[this, h]`. Establish `: (j : ℕ) < i + 1` using `by have : (j : ℕ) ≤ i := not_lt.mp h; omega`. Simplify using `[this, h]`. Rewrite `h1` using `[Finset.sum_congr rfl (fun j _ => s1 j), Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]`. Rewrite `h2` using `[Finset.sum_congr rfl (fun j _ => s2 j)]`.

Establish `h3 : X i * (R i (G i) + ∑ j : Fin r, (if i < j then X j * D i (G j) else 0)) = X i * 0`. Establish `e : ∀ j : Fin r, X i * (if i < j then X j * D i (G j) else 0) = (if i < j then X j * R i (G j) else 0) - (if i < j then X j * R (i + 1) (G j) else 0)`. Introduce `j`. Distinguish the cases in `h : i < j`. Simplify using `only [if_pos h]`.

Take the linear combination `(-(X j : MvPolynomial (Fin r) A)) * hD i (G j)`. Simplify using `[h]`. Rewrite using `[mul_add, Finset.mul_sum, Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, h2, mul_zero]`. Take the linear combination `h1`. Conclude with `(X_mul_cancel_left_iff).mp h3`.

Use `⟨fun i j => if j < i then D j (G i) else if i < j then -D i (G j) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `[h, not_lt.mpr h.le]`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, not_lt.mpr h.le]`. Introduce `i`. Simplify using the standard rewrite rules. Introduce `i`.

Establish `e : ∀ j : Fin r, X j * (if j < i then D j (G i) else if i < j then -D i (G j) else 0) = (if (j : ℕ) < i then X j * D j (G i) else 0) - (if i < j then X j * D i (G j) else 0)`. Introduce `j`. Break down `lt_trichotomy j i with h | h | h` into its components or cases. Establish `: (j : ℕ) < i` using `h`. Simplify using `[h, this, not_lt.mpr h.le]`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `: ¬ (j : ℕ) < i` using `by have : (i : ℕ) < j := h; omega`. Simplify using `[h, this, not_lt.mpr h.le]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, ← htel (G i) i (by omega)]`.

Take the linear combination `key i`.
-/
theorem koszul_relations_among_variables :
    ∀ (A : Type) [CommRing A] (r : ℕ) (G : Fin r → MvPolynomial (Fin r) A),
      ∑ i, X i * G i = 0 → ∃ H : Fin r → Fin r → MvPolynomial (Fin r) A,
        (∀ i j, H i j = -H j i) ∧ (∀ i, H i i = 0) ∧ ∀ i, G i = ∑ j, X j * H i j := by
  intro A _ r G hG

  let R : ℕ → MvPolynomial (Fin r) A →ₐ[A] MvPolynomial (Fin r) A :=
    fun n => aeval (fun j : Fin r => if (j : ℕ) < n then 0 else X j)
  have hRX : ∀ n (k : Fin r), R n (X k) = if (k : ℕ) < n then 0 else X k := by
    intro n k; simp [R]
  have hR0 : ∀ P, R 0 P = P := by
    intro P
    have : (fun j : Fin r => if (j : ℕ) < 0 then (0 : MvPolynomial (Fin r) A) else X j) = X := by
      funext j; simp
    simp only [R, this, aeval_X_left_apply]
  have hdvd : ∀ (i : Fin r) (P : MvPolynomial (Fin r) A), X i ∣ R i P - R (i + 1) P := by
    intro i P
    induction P using MvPolynomial.induction_on with
    | C a => simp [R]
    | add p q hp hq =>
      rw [map_add, map_add, add_sub_add_comm]; exact dvd_add hp hq
    | mul_X p k hp =>
      rw [map_mul, map_mul]
      have e : R i p * R i (X k) - R (i + 1) p * R (i + 1) (X k)
          = R i p * (R i (X k) - R (i + 1) (X k)) + (R i p - R (i + 1) p) * R (i + 1) (X k) := by
        ring
      rw [e]
      refine dvd_add (dvd_mul_of_dvd_right ?_ _) (dvd_mul_of_dvd_left hp _)
      rw [hRX, hRX]
      by_cases hki : k = i
      · subst hki; simp
      · have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
        by_cases hk : (k : ℕ) < i
        · simp [hk, show (k : ℕ) < i + 1 by omega]
        · simp [hk, show ¬ (k : ℕ) < i + 1 by omega]
  choose D hD using hdvd

  have htel : ∀ (P : MvPolynomial (Fin r) A) (n : ℕ), n ≤ r →
      P - R n P = ∑ j : Fin r, if (j : ℕ) < n then X j * D j P else 0 := by
    intro P n
    induction n with
    | zero => intro _; simp [hR0]
    | succ n ih =>
      intro hn
      have hlt : n < r := by omega
      have pt : ∀ j : Fin r, (if (j : ℕ) < n + 1 then X j * D j P else 0)
          = (if (j : ℕ) < n then X j * D j P else 0)
            + (if j = ⟨n, hlt⟩ then X j * D j P else 0) := by
        intro j
        by_cases h1 : (j : ℕ) < n
        · have : j ≠ ⟨n, hlt⟩ := fun h => by subst h; simp at h1
          simp [h1, this, show (j : ℕ) < n + 1 by omega]
        · by_cases h2 : (j : ℕ) = n
          · have : j = ⟨n, hlt⟩ := Fin.ext h2
            simp [h1, this]
          · have : j ≠ ⟨n, hlt⟩ := fun h => h2 (by rw [h])
            simp [h1, this, show ¬ (j : ℕ) < n + 1 by omega]
      rw [Finset.sum_congr rfl (fun j _ => pt j), Finset.sum_add_distrib, ← ih (by omega),
        Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _), ← hD]
      ring

  have hrel : ∀ n, ∑ j : Fin r, (if (j : ℕ) < n then 0 else X j) * R n (G j) = 0 := by
    intro n
    have := congrArg (R n) hG
    rw [map_sum, map_zero] at this
    simpa [map_mul, hRX] using this
  have key : ∀ i : Fin r, R i (G i) + ∑ j : Fin r, (if i < j then X j * D i (G j) else 0) = 0 := by
    intro i
    have h1 := hrel i
    have h2 := hrel (i + 1)
    have s1 : ∀ j : Fin r, (if (j : ℕ) < i then 0 else X j) * R i (G j)
        = (if j = i then X i * R i (G i) else 0) + (if i < j then X j * R i (G j) else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · have : (j : ℕ) < i := h
        simp [this, h.ne, not_lt.mpr h.le]
      · subst h; simp
      · have : ¬ (j : ℕ) < i := by have : (i : ℕ) < j := h; omega
        simp [this, h.ne', h]
    have s2 : ∀ j : Fin r, (if (j : ℕ) < i + 1 then 0 else X j) * R (i + 1) (G j)
        = (if i < j then X j * R (i + 1) (G j) else 0) := by
      intro j
      by_cases h : i < j
      · have : ¬ (j : ℕ) < i + 1 := by have : (i : ℕ) < j := h; omega
        simp [this, h]
      · have : (j : ℕ) < i + 1 := by have : (j : ℕ) ≤ i := not_lt.mp h; omega
        simp [this, h]
    rw [Finset.sum_congr rfl (fun j _ => s1 j), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)] at h1
    rw [Finset.sum_congr rfl (fun j _ => s2 j)] at h2
    have h3 : X i * (R i (G i) + ∑ j : Fin r, (if i < j then X j * D i (G j) else 0)) = X i * 0 := by
      have e : ∀ j : Fin r, X i * (if i < j then X j * D i (G j) else 0)
          = (if i < j then X j * R i (G j) else 0) - (if i < j then X j * R (i + 1) (G j) else 0) := by
        intro j
        by_cases h : i < j
        · simp only [if_pos h]
          linear_combination (-(X j : MvPolynomial (Fin r) A)) * hD i (G j)
        · simp [h]
      rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, h2,
        mul_zero]
      linear_combination h1
    exact (X_mul_cancel_left_iff).mp h3
  refine ⟨fun i j => if j < i then D j (G i) else if i < j then -D i (G j) else 0, ?_, ?_, ?_⟩
  · intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, not_lt.mpr h.le]
  · intro i; simp
  · intro i
    have e : ∀ j : Fin r, X j * (if j < i then D j (G i) else if i < j then -D i (G j) else 0)
        = (if (j : ℕ) < i then X j * D j (G i) else 0) - (if i < j then X j * D i (G j) else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · have : (j : ℕ) < i := h
        simp [h, this, not_lt.mpr h.le]
      · subst h; simp
      · have : ¬ (j : ℕ) < i := by have : (i : ℕ) < j := h; omega
        simp [h, this, not_lt.mpr h.le]
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, ← htel (G i) i (by omega)]
    linear_combination key i

end GlobalTheory
