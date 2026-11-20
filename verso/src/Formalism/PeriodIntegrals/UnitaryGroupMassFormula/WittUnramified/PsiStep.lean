import Mathlib
import Formalism.PeriodIntegrals.WittUnram

noncomputable section

namespace PI.WittUnramWork

open WittVector Finset

variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]

/- English proof (translation)
Use `(injective_iff_map_eq_zero ψ).2 ?_` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hne hirr`. Take `⟨u, hu⟩` from `hn`.

Establish `h2 : ψ ((p : W) ^ n) = 0` using `by rw [← hu, map_mul, hx, zero_mul]`. Rewrite `h2` using `[map_pow, map_natCast]`. Conclude with `pow_ne_zero n (WittVector.p_nonzero p k) h2`.
-/
theorem psi_injective (ψ : W →+* WittVector p k) (hirr : Irreducible (p : W)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 ?_
  intro x hx
  by_contra hne
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hirr
  obtain ⟨u, hu⟩ := hn
  have h2 : ψ ((p : W) ^ n) = 0 := by rw [← hu, map_mul, hx, zero_mul]
  rw [map_pow, map_natCast] at h2
  exact pow_ne_zero n (WittVector.p_nonzero p k) h2

/- English proof (translation)
Take `⟨a, ha⟩` from `hres (w.coeff 0)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hz : w - ψ a = 0`. Conclude with `⟨0, by rw [mul_zero, add_zero]; exact sub_eq_zero.mp hz⟩`. Take `⟨m, b, hb0, hb⟩` from `WittVector.exists_eq_pow_p_mul (w - ψ a) hz`.

Establish `hc : (w - ψ a).coeff 0 = 0`. Establish `h3` using `WittVector.add_coeff_zero (ψ a) (w - ψ a)`. Rewrite `h3` using `[show ψ a + (w - ψ a) = w by abel, h0, ha]`. Take the linear combination `-h3`. Establish `hm : m ≠ 0`.

Introduce and unpack `rfl`. Apply `hb0` to reduce the goal to its premises. Rewrite `hb` using `[pow_zero, one_mul]`. Rewrite using `[← hb]`. Conclude with `hc`.

Use `⟨(p : WittVector p k) ^ (m - 1) * b, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), ← hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_step (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (w : WittVector p k) :
    ∃ a : W, ∃ b : WittVector p k, w = ψ a + (p : WittVector p k) * b := by
  obtain ⟨a, ha⟩ := hres (w.coeff 0)
  refine ⟨a, ?_⟩
  by_cases hz : w - ψ a = 0
  · exact ⟨0, by rw [mul_zero, add_zero]; exact sub_eq_zero.mp hz⟩
  · obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ a) hz
    have hc : (w - ψ a).coeff 0 = 0 := by
      have h3 := WittVector.add_coeff_zero (ψ a) (w - ψ a)
      rw [show ψ a + (w - ψ a) = w by abel, h0, ha] at h3
      linear_combination -h3
    have hm : m ≠ 0 := by
      rintro rfl
      apply hb0
      rw [pow_zero, one_mul] at hb
      rw [← hb]
      exact hc
    refine ⟨(p : WittVector p k) ^ (m - 1) * b, ?_⟩
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), ← hb]
    ring

/- English proof (translation)
Introduce `w`. Use `choose A B hAB using psi_step ψ res hres h0`. Take `⟨r, hr0, hrs⟩ : ∃ r : ℕ → WittVector p k, r 0 = w ∧ ∀ n, r (n + 1) = B (r n)` from `⟨fun n => B^[n] w, rfl, fun n => Function.iterate_succ_apply' B n w⟩`. Take `⟨s, hs0, hss⟩ : ∃ s : ℕ → W, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + A (r n) * (p : W) ^ n` from `⟨fun n => ∑ i ∈ Finset.range n, A (r i) * (p : W) ^ i, by simp, fun n => Finset.sum_range_succ _ _⟩`. Establish `hinv : ∀ n, w = ψ (s n) + (p : WittVector p k) ^ n * r n`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [hs0, hr0, map_zero, pow_zero, one_mul, zero_add]`. Consider the case `succ n ih`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hAB (r n)]`. Use `_ = ψ (s (n + 1)) + (p : WittVector p k) ^ (n + 1) * r (n + 1) := by`. Rewrite using `[hss, hrs, map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiv : ∀ m n, m ≤ n → (p : W) ^ m ∣ s n - s m`.

Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[hss, add_sub_right_comm]`.

Conclude with `dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _)`. Establish `hI : ∀ n (x : W), x ∈ (Ideal.span {(p : W)} ^ n • ⊤ : Submodule W W) ↔ (p : W) ^ n ∣ x`. Introduce `n x`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨L, hL⟩` from `hC.toIsPrecomplete.prec (f := s) (fun {m n} hmn => by`.

Rewrite using `[SModEq.sub_mem, hI]`. Conclude with `dvd_sub_comm.mp (hdiv m n hmn))`. Establish `hw : ∀ n, (p : WittVector p k) ^ n ∣ w - ψ L`. Introduce `n`. Take `⟨c, hc⟩` from `(hI n _).1 (SModEq.sub_mem.1 (hL n))`.

Use `⟨ψ c + r n, ?_⟩` and prove the remaining obligations. Establish `h2 : ψ (s n) - ψ L = (p : WittVector p k) ^ n * ψ c`. Rewrite using `[← map_sub, hc, map_mul, map_pow, map_natCast]`. Combine the equalities or inequalities in the displayed calculation. Establish `hzero : w - ψ L = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨m, b, hb0, hb⟩` from `WittVector.exists_eq_pow_p_mul (w - ψ L) hne`. Take `⟨c, hc⟩` from `hw (m + 1)`. Rewrite `hc` using `[hb, pow_succ, mul_assoc]`. Establish `hp : (p : WittVector p k) ^ m ≠ 0` using `pow_ne_zero m (WittVector.p_nonzero p k)`.

Establish `hbc` using `mul_left_cancel₀ hp hc`. Apply `hb0` to reduce the goal to its premises. Rewrite using `[hbc]`. Use `first`. Consider the case `rw [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul]`.

Consider the case `simp`. Conclude with `⟨L, (sub_eq_zero.mp hzero).symm⟩`.
-/
theorem psi_surjective (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (hC : IsAdicComplete (Ideal.span {(p : W)}) W) :
    Function.Surjective ψ := by
  intro w
  choose A B hAB using psi_step ψ res hres h0
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → WittVector p k, r 0 = w ∧ ∀ n, r (n + 1) = B (r n) :=
    ⟨fun n => B^[n] w, rfl, fun n => Function.iterate_succ_apply' B n w⟩
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℕ → W, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + A (r n) * (p : W) ^ n :=
    ⟨fun n => ∑ i ∈ Finset.range n, A (r i) * (p : W) ^ i, by simp, fun n => Finset.sum_range_succ _ _⟩
  have hinv : ∀ n, w = ψ (s n) + (p : WittVector p k) ^ n * r n := by
    intro n
    induction n with
    | zero => rw [hs0, hr0, map_zero, pow_zero, one_mul, zero_add]
    | succ n ih =>
      calc w = ψ (s n) + (p : WittVector p k) ^ n * r n := ih
        _ = ψ (s n) + (p : WittVector p k) ^ n * (ψ (A (r n)) + (p : WittVector p k) * B (r n)) := by
          rw [← hAB (r n)]
        _ = ψ (s (n + 1)) + (p : WittVector p k) ^ (n + 1) * r (n + 1) := by
          rw [hss, hrs, map_add, map_mul, map_pow, map_natCast]
          ring
  have hdiv : ∀ m n, m ≤ n → (p : W) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hss, add_sub_right_comm]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _)
  have hI : ∀ n (x : W), x ∈ (Ideal.span {(p : W)} ^ n • ⊤ : Submodule W W) ↔ (p : W) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec (f := s) (fun {m n} hmn => by
    rw [SModEq.sub_mem, hI]
    exact dvd_sub_comm.mp (hdiv m n hmn))
  have hw : ∀ n, (p : WittVector p k) ^ n ∣ w - ψ L := by
    intro n
    obtain ⟨c, hc⟩ := (hI n _).1 (SModEq.sub_mem.1 (hL n))
    refine ⟨ψ c + r n, ?_⟩
    have h2 : ψ (s n) - ψ L = (p : WittVector p k) ^ n * ψ c := by
      rw [← map_sub, hc, map_mul, map_pow, map_natCast]
    calc w - ψ L = ψ (s n) + (p : WittVector p k) ^ n * r n - ψ L := by rw [← hinv n]
      _ = (p : WittVector p k) ^ n * (ψ c + r n) := by linear_combination h2
  have hzero : w - ψ L = 0 := by
    by_contra hne
    obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ L) hne
    obtain ⟨c, hc⟩ := hw (m + 1)
    rw [hb, pow_succ, mul_assoc] at hc
    have hp : (p : WittVector p k) ^ m ≠ 0 := pow_ne_zero m (WittVector.p_nonzero p k)
    have hbc := mul_left_cancel₀ hp hc
    apply hb0
    rw [hbc]
    first
    | rw [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul]
    | simp
  exact ⟨L, (sub_eq_zero.mp hzero).symm⟩

end PI.WittUnramWork
