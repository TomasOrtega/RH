import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open GlobalTheory.LeviCut

namespace GlobalTheory.BetaDenProof

/- English proof (translation)
Establish `ht0 : t ≠ 0` using `by omega`. Use `conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self t l]`. Rewrite using `[mul_comm (ordProj[l] t)]`. Apply `Nat.mul_dvd_mul` to reduce the goal to its premises. Conclude with `Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨ht, htw⟩)`.

Apply `Nat.pow_dvd_pow` to reduce the goal to its premises. Apply `Nat.le_log_of_pow_le hl.one_lt` to reduce the goal to its premises. Conclude with `(Nat.ordProj_le l ht0).trans htw`.
-/
theorem dvd_lam_of_le {l w t : ℕ} (hl : l.Prime) (ht : 1 ≤ t) (htw : t ≤ w) :
    t ∣ (∏ s ∈ Finset.Icc 1 w, ordCompl[l] s) * l ^ Nat.log l w := by
  have ht0 : t ≠ 0 := by omega
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self t l]
  rw [mul_comm (ordProj[l] t)]
  apply Nat.mul_dvd_mul
  · exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨ht, htw⟩)
  · apply Nat.pow_dvd_pow
    apply Nat.le_log_of_pow_le hl.one_lt
    exact (Nat.ordProj_le l ht0).trans htw

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `j hj`. Simplify using `only [Nat.add_zero, Nat.factorial_zero, mul_one, Nat.factorial_succ]`.

Conclude with `Nat.mul_dvd_mul (h (j + 1) (by omega) (by omega)) dvd_rfl`. Consider the case `succ k ih`. Introduce `j hj`. Establish `h1` using `ih j (by omega)`. Establish `h2` using `ih (j + 1) (by omega)`.

Establish `e : Λ * (j.factorial * (k + 1).factorial) + Λ * ((j + 1).factorial * k.factorial) = (j + k + 2) * (Λ * (j.factorial * k.factorial))`. Rewrite using `[Nat.factorial_succ k, Nat.factorial_succ j]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : (j + (k + 1) + 1).factorial ∣ (j + k + 2) * (Λ * (j.factorial * k.factorial))`. Establish `: (j + (k + 1) + 1).factorial = (j + k + 2) * (j + k + 1).factorial`.

Rewrite using `[show j + (k + 1) + 1 = (j + k + 1) + 1 by omega, Nat.factorial_succ]`. Rewrite using `[this]`. Conclude with `Nat.mul_dvd_mul dvd_rfl h1`. Establish `hB : (j + (k + 1) + 1).factorial ∣ Λ * ((j + 1).factorial * k.factorial)`. Rewrite using `[show j + (k + 1) + 1 = j + 1 + k + 1 by omega]; exact h2`.

Rewrite `hA` using `[← e]`. Conclude with `(Nat.dvd_add_left hB).mp hA`.
-/
theorem beta_dvd {Λ w : ℕ} (h : ∀ t, 1 ≤ t → t ≤ w → t ∣ Λ) :
    ∀ k j : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial) := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp only [Nat.add_zero, Nat.factorial_zero, mul_one, Nat.factorial_succ]
    exact Nat.mul_dvd_mul (h (j + 1) (by omega) (by omega)) dvd_rfl
  | succ k ih =>
    intro j hj
    have h1 := ih j (by omega)
    have h2 := ih (j + 1) (by omega)
    have e : Λ * (j.factorial * (k + 1).factorial) + Λ * ((j + 1).factorial * k.factorial)
        = (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      rw [Nat.factorial_succ k, Nat.factorial_succ j]; ring
    have hA : (j + (k + 1) + 1).factorial ∣ (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      have : (j + (k + 1) + 1).factorial = (j + k + 2) * (j + k + 1).factorial := by
        rw [show j + (k + 1) + 1 = (j + k + 1) + 1 by omega, Nat.factorial_succ]
      rw [this]; exact Nat.mul_dvd_mul dvd_rfl h1
    have hB : (j + (k + 1) + 1).factorial ∣ Λ * ((j + 1).factorial * k.factorial) := by
      rw [show j + (k + 1) + 1 = j + 1 + k + 1 by omega]; exact h2
    rw [← e] at hA
    exact (Nat.dvd_add_left hB).mp hA

end GlobalTheory.BetaDenProof

/- English proof (translation)
Introduce `l w hl`. Use `⟨∏ s ∈ Finset.Icc 1 w, ordCompl[l] s, ?_, ?_⟩` and prove the remaining obligations. Introduce `hd`. Take `⟨s, hs, hds⟩` from `(Prime.dvd_finset_prod_iff hl.prime _).mp hd`. Establish `: s ≠ 0` using `by have := (Finset.mem_Icc.mp hs).1; omega`.

Conclude with `Nat.not_dvd_ordCompl hl this hds`. Introduce `j k hjk`. Conclude with `GlobalTheory.BetaDenProof.beta_dvd (fun t ht htw => GlobalTheory.BetaDenProof.dvd_lam_of_le hl ht htw) k j hjk`.
-/
theorem GlobalTheory.LeviCut.betaDen : GlobalTheory.LeviCut.BetaDen := by
  intro l w hl
  refine ⟨∏ s ∈ Finset.Icc 1 w, ordCompl[l] s, ?_, ?_⟩
  · intro hd
    obtain ⟨s, hs, hds⟩ := (Prime.dvd_finset_prod_iff hl.prime _).mp hd
    have : s ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
    exact Nat.not_dvd_ordCompl hl this hds
  · intro j k hjk
    exact GlobalTheory.BetaDenProof.beta_dvd (fun t ht htw => GlobalTheory.BetaDenProof.dvd_lam_of_le hl ht htw) k j hjk
