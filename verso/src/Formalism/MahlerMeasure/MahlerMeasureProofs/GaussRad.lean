import Formalism.MahlerMeasure.StatementD

namespace Formalism.GM

open Finset Polynomial

section

variable {K : Type} [NormedField K]

/- English proof (translation)
Distinguish the cases in `hk : k ∈ P.support`. Conclude with `Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk`. Establish `h0 : P.coeff k = 0` using `by simpa using hk`. Simplify using `[h0]`.
-/
lemma gaussR_term_le (ρ : NNReal) (P : K[X]) (k : ℕ) :
    ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P := by
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · have h0 : P.coeff k = 0 := by simpa using hk
    simp [h0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h k => (gaussR_term_le ρ P k).trans h, fun h => Finset.sup_le fun k _ => h k⟩`.
-/
lemma gaussR_le_iff (ρ : NNReal) (P : K[X]) (c : NNReal) :
    gaussR ρ P ≤ c ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ c := ⟨fun h k => (gaussR_term_le ρ P k).trans h, fun h => Finset.sup_le fun k _ => h k⟩

/- English proof (translation)
Take `⟨k, -, hk⟩` from `Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP) (fun k => ‖P.coeff k‖₊ * ρ ^ k)`. Conclude with `⟨k, hk.symm⟩`.
-/
lemma gaussR_attained (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ k, ‖P.coeff k‖₊ * ρ ^ k = gaussR ρ P := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  exact ⟨k, hk.symm⟩

/- English proof (translation)
Establish `h` using `gaussR_attained ρ P hP`. Conclude with `⟨Nat.find h, Nat.find_spec h, fun i hi => lt_of_le_of_ne (gaussR_term_le ρ P i) (Nat.find_min h hi)⟩`.
-/
lemma gaussR_attained_least (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ i₀, ‖P.coeff i₀‖₊ * ρ ^ i₀ = gaussR ρ P ∧
      ∀ i < i₀, ‖P.coeff i‖₊ * ρ ^ i < gaussR ρ P := by
  classical
  have h := gaussR_attained ρ P hP
  exact ⟨Nat.find h, Nat.find_spec h, fun i hi => lt_of_le_of_ne (gaussR_term_le ρ P i) (Nat.find_min h hi)⟩

/- English proof (translation)
Take `⟨k, hk, hk'⟩` from `Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP) (fun k => ‖P.coeff k‖₊ * ρ ^ k)`. Unfold `gaussR`. Rewrite using `[hk']`. Conclude with `mul_pos (nnnorm_pos.2 (Polynomial.mem_support_iff.1 hk)) (pow_pos hρ k)`.
-/
lemma gaussR_pos (ρ : NNReal) (hρ : 0 < ρ) (P : K[X]) (hP : P ≠ 0) : 0 < gaussR ρ P := by
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  unfold gaussR
  rw [hk']
  exact mul_pos (nnnorm_pos.2 (Polynomial.mem_support_iff.1 hk)) (pow_pos hρ k)

/- English proof (translation)
Simplify using `[gaussR]`.
-/
lemma gaussR_zero (ρ : NNReal) : gaussR ρ (0 : K[X]) = 0 := by
  simp [gaussR]

variable [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[gaussR_le_iff]`. Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Establish `h1 : ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊)` using `IsUltrametricDist.nnnorm_sum_le_of_forall_le (fun x hx => Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) hx)`. Take `⟨x, hx, hxe⟩` from `Finset.exists_mem_eq_sup (Finset.HasAntidiagonal.antidiagonal k) ⟨(0, k), by simp⟩ (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊)`.

Establish `hk : x.1 + x.2 = k` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hx`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[nnnorm_mul, ← hk, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ gaussR ρ P * gaussR ρ Q := mul_le_mul' (gaussR_term_le ρ P _) (gaussR_term_le ρ Q _)`.
-/
lemma gaussR_mul_le (ρ : NNReal) (P Q : K[X]) :
    gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by
  rw [gaussR_le_iff]
  intro k
  rw [Polynomial.coeff_mul]
  have h1 : ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ ≤
      (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) :=
    IsUltrametricDist.nnnorm_sum_le_of_forall_le
      (fun x hx => Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) hx)
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup (Finset.HasAntidiagonal.antidiagonal k) ⟨(0, k), by simp⟩
    (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊)
  have hk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  calc ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k
      ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) * ρ ^ k :=
        mul_le_mul_of_nonneg_right h1 zero_le
    _ = ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k := by rw [hxe]
    _ = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
        rw [nnnorm_mul, ← hk, pow_add]
        ring
    _ ≤ gaussR ρ P * gaussR ρ Q := mul_le_mul' (gaussR_term_le ρ P _) (gaussR_term_le ρ Q _)

/- English proof (translation)
Distinguish the cases in `hP : P = 0`. Simplify using `[hP, gaussR_zero]`. Distinguish the cases in `hQ : Q = 0`. Simplify using `[hQ, gaussR_zero]`. Take `⟨i₀, hi₀, hlt_i⟩` from `gaussR_attained_least ρ P hP`.

Take `⟨j₀, hj₀, hlt_j⟩` from `gaussR_attained_least ρ Q hQ`. Establish `hgP` using `gaussR_pos ρ hρ P hP`. Establish `hgQ` using `gaussR_pos ρ hρ Q hQ`. Establish `hρk : 0 < ρ ^ (i₀ + j₀)` using `pow_pos hρ _`. Establish `hsplit : (P * Q).coeff (i₀ + j₀) = P.coeff i₀ * Q.coeff j₀ + ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2`.

Establish `hmem : ((i₀, j₀) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)` using `Finset.HasAntidiagonal.mem_antidiagonal.2 rfl`. Rewrite using `[Polynomial.coeff_mul, Finset.add_sum_erase _ (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem]`. Establish `hterm : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q`. Introduce `x hx`. Take `⟨hne, hx'⟩` from `Finset.mem_erase.1 hx`.

Establish `hsum : x.1 + x.2 = i₀ + j₀` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hx'`. Establish `e : ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)`. Rewrite using `[nnnorm_mul, ← hsum, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Distinguish the cases in `h1 : x.1 < i₀`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : x.2 < j₀`. Assume the negation of the conclusion as `h`. Conclude with `hne (Prod.ext (by omega) (by omega))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsup : ((Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀)).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) < gaussR ρ P * gaussR ρ Q` using `(Finset.sup_lt_iff (mul_pos hgP hgQ)).2 hterm`. Establish `hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q`. Use `lt_of_le_of_lt ?_ hsup` and prove the remaining obligations. Rewrite using `[← le_div_iff₀ hρk]`.

Apply `IsUltrametricDist.nnnorm_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[le_div_iff₀ hρk]`. Conclude with `Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) hx`. Establish `hmain : ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) = gaussR ρ P * gaussR ρ Q`.

Rewrite using `[nnnorm_mul, pow_add, ← hi₀, ← hj₀]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀)`. Rewrite using `[hmain]`. Conclude with `hrest`.

Establish `hlt` using `lt_of_mul_lt_mul_right h' zero_le`. Establish `heq : ‖(P * Q).coeff (i₀ + j₀)‖₊ = ‖P.coeff i₀ * Q.coeff j₀‖₊`. Rewrite using `[hsplit, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hlt.ne', max_eq_left hlt.le]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma le_gaussR_mul (ρ : NNReal) (hρ : 0 < ρ) (P Q : K[X]) :
    gaussR ρ P * gaussR ρ Q ≤ gaussR ρ (P * Q) := by
  by_cases hP : P = 0
  · simp [hP, gaussR_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gaussR_zero]
  obtain ⟨i₀, hi₀, hlt_i⟩ := gaussR_attained_least ρ P hP
  obtain ⟨j₀, hj₀, hlt_j⟩ := gaussR_attained_least ρ Q hQ
  have hgP := gaussR_pos ρ hρ P hP
  have hgQ := gaussR_pos ρ hρ Q hQ
  have hρk : 0 < ρ ^ (i₀ + j₀) := pow_pos hρ _
  have hsplit : (P * Q).coeff (i₀ + j₀) = P.coeff i₀ * Q.coeff j₀ +
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2 := by
    have hmem : ((i₀, j₀) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    rw [Polynomial.coeff_mul, Finset.add_sum_erase _ (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem]
  have hterm : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    intro x hx
    obtain ⟨hne, hx'⟩ := Finset.mem_erase.1 hx
    have hsum : x.1 + x.2 = i₀ + j₀ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx'
    have e : ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) =
        (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
      rw [nnnorm_mul, ← hsum, pow_add]
      ring
    rw [e]
    by_cases h1 : x.1 < i₀
    · calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ (‖P.coeff x.1‖₊ * ρ ^ x.1) * gaussR ρ Q := mul_le_mul_of_nonneg_left (gaussR_term_le ρ Q _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_right (hlt_i _ h1) hgQ
    · have h2 : x.2 < j₀ := by
        by_contra h
        exact hne (Prod.ext (by omega) (by omega))
      calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ gaussR ρ P * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := mul_le_mul_of_nonneg_right (gaussR_term_le ρ P _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_left (hlt_j _ h2) hgP
  have hsup : ((Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀)).sup
      (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) < gaussR ρ P * gaussR ρ Q :=
    (Finset.sup_lt_iff (mul_pos hgP hgQ)).2 hterm
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    refine lt_of_le_of_lt ?_ hsup
    rw [← le_div_iff₀ hρk]
    apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
    intro x hx
    rw [le_div_iff₀ hρk]
    exact Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) hx
  have hmain : ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) = gaussR ρ P * gaussR ρ Q := by
    rw [nnnorm_mul, pow_add, ← hi₀, ← hj₀]
    ring
  have h' : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) := by
    rw [hmain]
    exact hrest
  have hlt := lt_of_mul_lt_mul_right h' zero_le
  have heq : ‖(P * Q).coeff (i₀ + j₀)‖₊ = ‖P.coeff i₀ * Q.coeff j₀‖₊ := by
    rw [hsplit, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hlt.ne', max_eq_left hlt.le]
  calc gaussR ρ P * gaussR ρ Q = ‖(P * Q).coeff (i₀ + j₀)‖₊ * ρ ^ (i₀ + j₀) := by rw [heq, hmain]
    _ ≤ gaussR ρ (P * Q) := gaussR_term_le ρ (P * Q) _

end

/- English proof (translation)
Introduce `K _ _ ρ P Q hρ` and use `le_antisymm (gaussR_mul_le ρ P Q) (le_gaussR_mul ρ hρ P Q)`.
-/
theorem gauss_norm_multiplicative : GaussMulRad := fun K _ _ ρ P Q hρ => le_antisymm (gaussR_mul_le ρ P Q) (le_gaussR_mul ρ hρ P Q)

end Formalism.GM
