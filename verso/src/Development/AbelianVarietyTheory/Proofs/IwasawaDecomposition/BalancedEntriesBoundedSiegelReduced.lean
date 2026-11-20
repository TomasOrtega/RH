import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelUnipotentInverseEntriesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedIntMatrixTriangularGramAdjointWeightedSqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelDomainLowerBlockEqZeroOfLargeGapStatement

noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem term_le_double_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ p q, 0 ≤ f p q) (p q : Fin n) :
    f p q ≤ ∑ p, ∑ q, f p q := by
  calc f p q ≤ ∑ q, f p q := Finset.single_le_sum (fun q _ => hf p q) (Finset.mem_univ q)
    _ ≤ ∑ p, ∑ q, f p q := Finset.single_le_sum (f := fun p => ∑ q, f p q)
        (fun p _ => Finset.sum_nonneg fun q _ => hf p q) (Finset.mem_univ p)

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro hm`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `hm`. Establish `h1` using `ih (by omega)`. Establish `h2` using `hs ⟨q + m, by omega⟩ ⟨q + (m + 1), hm⟩ (by simp; omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem step_chain {n : ℕ} {d : Fin n → ℝ} (hs : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q)
    (q : Fin n) : ∀ m (hm : (q : ℕ) + m < n), d q ≤ 4 ^ m * d ⟨q + m, hm⟩ := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hs ⟨q + m, by omega⟩ ⟨q + (m + 1), hm⟩ (by simp; omega)
    calc d q ≤ 4 ^ m * d ⟨q + m, by omega⟩ := h1
      _ ≤ 4 ^ m * (4 * d ⟨q + (m + 1), hm⟩) := by gcongr
      _ = 4 ^ (m + 1) * d ⟨q + (m + 1), hm⟩ := by ring

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro hm _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `hm h`. Establish `h1` using `ih (by omega) (fun k k' hk hpk hk' => h k k' hk hpk (by omega))`. Establish `h2` using `h ⟨p + m, by omega⟩ ⟨p + (m + 1), hm⟩ (by simp; omega) (by simp [Fin.le_def]) (by simp)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gap_chain {n : ℕ} {d : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R) (p : Fin n) :
    ∀ m (hm : (p : ℕ) + m < n),
      (∀ k k' : Fin n, (k' : ℕ) = k + 1 → p ≤ k → (k' : ℕ) ≤ p + m → d k' ≤ R * d k) →
      d ⟨p + m, hm⟩ ≤ R ^ m * d p := by
  intro m
  induction m with
  | zero => intro hm _; simp
  | succ m ih =>
    intro hm h
    have h1 := ih (by omega) (fun k k' hk hpk hk' => h k k' hk hpk (by omega))
    have h2 := h ⟨p + m, by omega⟩ ⟨p + (m + 1), hm⟩ (by simp; omega)
      (by simp [Fin.le_def]) (by simp)
    calc d ⟨p + (m + 1), hm⟩ ≤ R * d ⟨p + m, by omega⟩ := h2
      _ ≤ R * (R ^ m * d p) := by gcongr
      _ = R ^ (m + 1) * d p := by ring

/- English proof (translation)
Introduce `n K`. Take `⟨c, hc⟩` from `GlobalTheory.T.siegelUnipotent_inverse_entries_bounded n`. Take `⟨R, hR1, hR⟩` from `GlobalTheory.T.siegelDomain_lowerBlock_eq_zero_of_large_gap n K c`. Establish `hK0 : 0 ≤ max K 0` using `le_max_right _ _`. Establish `h4 : (1 : ℝ) ≤ 4 ^ n` using `one_le_pow₀ (by norm_num)`.

Establish `hRn : (1 : ℝ) ≤ R ^ n` using `one_le_pow₀ hR1`. Establish `hB : 0 ≤ 4 ^ n * R ^ n * max K 0`. Apply `mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0` to reduce the goal to its premises. Use `⟨(n : ℝ) ^ 2 * |c| * (1 + 4 ^ n * R ^ n * max K 0), ?_⟩` and prove the remaining obligations. Introduce `A A' d u hS hd hbal htr i j`.

Take `⟨v, hvu, huv, hvl, hvc⟩` from `hc u hS.diag hS.lower hS.upper`. Take `⟨hsym, hsum, hsum'⟩` from `GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace n A A' d u v hd hvu huv hbal`. Establish `hK' : ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K`. Rewrite using `[hsum']`. Conclude with `htr`.

Establish `hK : ∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K`. Rewrite using `[hsum]`. Conclude with `htr`. Use `set Ar := A.map (Int.cast : ℤ → ℝ) with hAr`. Use `set W := u * Ar * v with hWdef`.

Use `set B := 4 ^ n * R ^ n * max K 0 with hBdef`. Establish `hterm : ∀ p q, d p / d q * W p q ^ 2 ≤ max K 0` using `fun p q => (term_le_double_sum (fun p q => d p / d q * W p q ^ 2) (fun p q => mul_nonneg (div_nonneg (hd p).le (hd q).le) (sq_nonneg _)) p q).trans (hK.trans (le_max_left _ _))`. Establish `hsq : ∀ p q, W p q ^ 2 ≤ d q / d p * max K 0`. Introduce `p q`. Establish `hp` using `(hd p).ne'`.

Establish `hq` using `(hd q).ne'`. Establish `e : W p q ^ 2 = d q / d p * (d p / d q * W p q ^ 2)` using `by field_simp`. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_left (hterm p q) (div_nonneg (hd q).le (hd p).le)`. Establish `hW : ∀ p q, W p q ^ 2 ≤ B`.

Introduce `p q`. Break down `le_or_gt q p with hqp | hpq` into its components or cases. Establish `hqp' : (q : ℕ) ≤ p` using `hqp`. Establish `hm : (q : ℕ) + ((p : ℕ) - q) < n` using `by omega`. Establish `h1` using `step_chain hS.step q ((p : ℕ) - q) hm`.

Establish `hpe : (⟨(q : ℕ) + ((p : ℕ) - q), hm⟩ : Fin n) = p` using `by ext; simp; omega`. Rewrite `h1` using `[hpe]`. Establish `h2 : (4 : ℝ) ^ ((p : ℕ) - q) ≤ 4 ^ n` using `pow_le_pow_right₀ (by norm_num) (by omega)`. Establish `h3 : d q ≤ 4 ^ n * d p` using `h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)`. Establish `h5 : d q / d p ≤ 4 ^ n` using `by rw [div_le_iff₀ (hd p)]; exact h3`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpq' : (p : ℕ) < q` using `hpq`. Distinguish the cases in `hgap : ∃ k k' : Fin n, (k' : ℕ) = k + 1 ∧ p ≤ k ∧ k' ≤ q ∧ R * d k < d k'`. Take `⟨k, k', hk, hpk, hkq, hlt⟩` from `hgap`. Establish `h0 : (u * A'.map (Int.cast : ℤ → ℝ) * v) q p = 0` using `hR A' d u v hS hd hvu huv hvl hvc hK' k k' hk hlt q p hpk hkq`.

Establish `h1` using `hsym p q`. Rewrite `h1` using `[h0, mul_zero]`. Establish `hz : W p q = 0`. Break down `mul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `absurd h (hd p).ne'`.

Conclude with `h`. Rewrite using `[hz]`. Simplify using `using hB`. Use `push_neg at hgap`. Establish `hm : (p : ℕ) + ((q : ℕ) - p) < n` using `by omega`.

Establish `h1` using `gap_chain (d := d) (by linarith) p ((q : ℕ) - p) hm (fun k k' hk hpk hk' => hgap k k' hk hpk (by rw [Fin.le_def]; omega))`. Establish `hqe : (⟨(p : ℕ) + ((q : ℕ) - p), hm⟩ : Fin n) = q` using `by ext; simp; omega`. Rewrite `h1` using `[hqe]`. Establish `h2 : R ^ ((q : ℕ) - p) ≤ R ^ n` using `pow_le_pow_right₀ hR1 (by omega)`. Establish `h3 : d q ≤ R ^ n * d p` using `h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)`.

Establish `h5 : d q / d p ≤ R ^ n` using `by rw [div_le_iff₀ (hd p)]; exact h3`. Combine the equalities or inequalities in the displayed calculation. Establish `hA : Ar = v * W * u`. Combine the equalities or inequalities in the displayed calculation. Establish `hu1 : ∀ l j, |u l j| ≤ 1`.

Introduce `l j`. Break down `lt_trichotomy l j with h | h | h` into its components or cases. Conclude with `(hS.upper l j h).trans (by norm_num)`. Substitute `h` using the available equality. Rewrite using `[hS.diag]`.

Simplify using the standard rewrite rules. Rewrite using `[hS.lower l j h]`. Simplify using the standard rewrite rules. Establish `hWb : ∀ k l, |W k l| ≤ 1 + B` using `fun k l => by`. Use polynomial arithmetic with `[hW k l, abs_nonneg (W k l), sq_abs (W k l)]`.

Establish `hc0 : 0 ≤ |c|` using `abs_nonneg c`. Apply the tactic sequence `have hentry : |Ar i j| ≤ (n : ℝ) ^ 2 * |c| * (1 + B) := by`. Rewrite using `[hA, Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `l _`. Rewrite using `[abs_mul, Matrix.mul_apply]`. Establish `hin : |∑ k, v i k * W k l| ≤ (n : ℝ) * (|c| * (1 + B))`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `k _`. Rewrite using `[abs_mul]`. Conclude with `mul_le_mul ((hvc i k).trans (le_abs_self c)) (hWb k l) (abs_nonneg _) hc0`. Use `_ = (n : ℝ) * (|c| * (1 + B)) := by simp`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = (n : ℝ) ^ 2 * |c| * (1 + B) := by simp; ring`. Establish `hcast : ((|A i j| : ℤ) : ℝ) = |Ar i j|` using `by simp [hAr, Int.cast_abs]`. Rewrite using `[hcast]`. Conclude with `hentry`.
-/
theorem balanced_entries_bounded : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) →
    (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) →
    (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  intro n K
  obtain ⟨c, hc⟩ := GlobalTheory.T.siegelUnipotent_inverse_entries_bounded n
  obtain ⟨R, hR1, hR⟩ := GlobalTheory.T.siegelDomain_lowerBlock_eq_zero_of_large_gap n K c
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hRn : (1 : ℝ) ≤ R ^ n := one_le_pow₀ hR1
  have hB : 0 ≤ 4 ^ n * R ^ n * max K 0 := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0
  refine ⟨(n : ℝ) ^ 2 * |c| * (1 + 4 ^ n * R ^ n * max K 0), ?_⟩
  intro A A' d u hS hd hbal htr i j
  obtain ⟨v, hvu, huv, hvl, hvc⟩ := hc u hS.diag hS.lower hS.upper
  obtain ⟨hsym, hsum, hsum'⟩ := GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace n A A' d u v hd hvu huv hbal
  have hK' : ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum']; exact htr
  have hK : ∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum]; exact htr
  set Ar := A.map (Int.cast : ℤ → ℝ) with hAr
  set W := u * Ar * v with hWdef
  set B := 4 ^ n * R ^ n * max K 0 with hBdef
  have hterm : ∀ p q, d p / d q * W p q ^ 2 ≤ max K 0 := fun p q =>
    (term_le_double_sum (fun p q => d p / d q * W p q ^ 2)
      (fun p q => mul_nonneg (div_nonneg (hd p).le (hd q).le) (sq_nonneg _)) p q).trans
      (hK.trans (le_max_left _ _))
  have hsq : ∀ p q, W p q ^ 2 ≤ d q / d p * max K 0 := by
    intro p q
    have hp := (hd p).ne'
    have hq := (hd q).ne'
    have e : W p q ^ 2 = d q / d p * (d p / d q * W p q ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hterm p q) (div_nonneg (hd q).le (hd p).le)
  have hW : ∀ p q, W p q ^ 2 ≤ B := by
    intro p q
    rcases le_or_gt q p with hqp | hpq
    · have hqp' : (q : ℕ) ≤ p := hqp
      have hm : (q : ℕ) + ((p : ℕ) - q) < n := by omega
      have h1 := step_chain hS.step q ((p : ℕ) - q) hm
      have hpe : (⟨(q : ℕ) + ((p : ℕ) - q), hm⟩ : Fin n) = p := by ext; simp; omega
      rw [hpe] at h1
      have h2 : (4 : ℝ) ^ ((p : ℕ) - q) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : d q ≤ 4 ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
      have h5 : d q / d p ≤ 4 ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
      calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
        _ ≤ 4 ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
        _ ≤ 4 ^ n * max K 0 * R ^ n := le_mul_of_one_le_right (by positivity) hRn
        _ = B := by rw [hBdef]; ring
    · have hpq' : (p : ℕ) < q := hpq
      by_cases hgap : ∃ k k' : Fin n, (k' : ℕ) = k + 1 ∧ p ≤ k ∧ k' ≤ q ∧ R * d k < d k'
      · obtain ⟨k, k', hk, hpk, hkq, hlt⟩ := hgap
        have h0 : (u * A'.map (Int.cast : ℤ → ℝ) * v) q p = 0 :=
          hR A' d u v hS hd hvu huv hvl hvc hK' k k' hk hlt q p hpk hkq
        have h1 := hsym p q
        rw [h0, mul_zero] at h1
        have hz : W p q = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (hd p).ne'
          · exact h
        rw [hz]
        simpa using hB
      · push_neg at hgap
        have hm : (p : ℕ) + ((q : ℕ) - p) < n := by omega
        have h1 := gap_chain (d := d) (by linarith) p ((q : ℕ) - p) hm
          (fun k k' hk hpk hk' => hgap k k' hk hpk (by rw [Fin.le_def]; omega))
        have hqe : (⟨(p : ℕ) + ((q : ℕ) - p), hm⟩ : Fin n) = q := by ext; simp; omega
        rw [hqe] at h1
        have h2 : R ^ ((q : ℕ) - p) ≤ R ^ n := pow_le_pow_right₀ hR1 (by omega)
        have h3 : d q ≤ R ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
        have h5 : d q / d p ≤ R ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
        calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
          _ ≤ R ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
          _ ≤ 4 ^ n * (R ^ n * max K 0) := le_mul_of_one_le_left (by positivity) h4
          _ = B := by rw [hBdef]; ring
  have hA : Ar = v * W * u := by
    calc Ar = (v * u) * Ar * (v * u) := by rw [hvu, Matrix.one_mul, Matrix.mul_one]
      _ = v * W * u := by rw [hWdef]; simp only [Matrix.mul_assoc]
  have hu1 : ∀ l j, |u l j| ≤ 1 := by
    intro l j
    rcases lt_trichotomy l j with h | h | h
    · exact (hS.upper l j h).trans (by norm_num)
    · subst h; rw [hS.diag]; simp
    · rw [hS.lower l j h]; simp
  have hWb : ∀ k l, |W k l| ≤ 1 + B := fun k l => by
    nlinarith [hW k l, abs_nonneg (W k l), sq_abs (W k l)]
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hentry : |Ar i j| ≤ (n : ℝ) ^ 2 * |c| * (1 + B) := by
    rw [hA, Matrix.mul_apply]
    calc |∑ l, (v * W) i l * u l j| ≤ ∑ l, |(v * W) i l * u l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, (n : ℝ) * (|c| * (1 + B)) := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, Matrix.mul_apply]
        have hin : |∑ k, v i k * W k l| ≤ (n : ℝ) * (|c| * (1 + B)) := by
          calc |∑ k, v i k * W k l| ≤ ∑ k, |v i k * W k l| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k : Fin n, |c| * (1 + B) := by
              apply Finset.sum_le_sum; intro k _
              rw [abs_mul]
              exact mul_le_mul ((hvc i k).trans (le_abs_self c)) (hWb k l) (abs_nonneg _) hc0
            _ = (n : ℝ) * (|c| * (1 + B)) := by simp
        calc |∑ k, v i k * W k l| * |u l j| ≤ (n : ℝ) * (|c| * (1 + B)) * 1 :=
              mul_le_mul hin (hu1 l j) (abs_nonneg _) (by positivity)
          _ = (n : ℝ) * (|c| * (1 + B)) := by ring
      _ = (n : ℝ) ^ 2 * |c| * (1 + B) := by simp; ring
  have hcast : ((|A i j| : ℤ) : ℝ) = |Ar i j| := by simp [hAr, Int.cast_abs]
  rw [hcast]
  exact hentry

end GlobalTheory.RedTh
