import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFrobeniusCharP
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Conclude with `⟨0, 0, Y, fun i => by simp, fun i => by simpa using hY i⟩`. Consider the case `succ n ih`. Take `⟨B, Z, Yn, h1, h2⟩` from `ih`.

Take `⟨B', Z', Y', h3, h4⟩` from `GlobalTheory.LemY.step p S K d U Z Yn h2`. Use `⟨fun i => B i + (p : WittVector p S) ^ n * B' i, Z', Y', fun i => ?_, h4⟩` and prove the remaining obligations. Rewrite using `[h1 i, h3 i, map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem digits (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p]
    [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ)
    (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Y : Fin d → WittVector p K)
    (hY : ∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i) (n : ℕ) :
    ∃ (B Z : Fin d → WittVector p S) (Yn : Fin d → WittVector p K),
      (∀ i, Y i = WittVector.map (algebraMap S K) (B i) + (p : WittVector p K) ^ n * Yn i) ∧
      ∀ i, WittVector.frobenius (Yn i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Yn) i
        + WittVector.map (algebraMap S K) (Z i) := by
  induction n with
  | zero =>
    exact ⟨0, 0, Y, fun i => by simp, fun i => by simpa using hY i⟩
  | succ n ih =>
    obtain ⟨B, Z, Yn, h1, h2⟩ := ih
    obtain ⟨B', Z', Y', h3, h4⟩ := GlobalTheory.LemY.step p S K d U Z Yn h2
    refine ⟨fun i => B i + (p : WittVector p S) ^ n * B' i, Z', Y', fun i => ?_, h4⟩
    rw [h1 i, h3 i, map_add, map_mul, map_pow, map_natCast]
    ring

/- English proof (translation)
Establish `h` using `(WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (x := a + (p : WittVector p K) ^ n * y) (y := a) (n := n)).2 (fun m hm => by`. Rewrite using `[add_sub_cancel_left, mul_comm]`. Conclude with `WittVector.mul_pow_charP_coeff_zero _ hm)`. Conclude with `h k hk`.
-/
theorem coeff_add_p_pow_mul_lt (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p] (n k : ℕ)
    (hk : k < n) (a y : WittVector p K) : (a + (p : WittVector p K) ^ n * y).coeff k = a.coeff k := by
  have h := (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (x := a + (p : WittVector p K) ^ n * y)
    (y := a) (n := n)).2 (fun m hm => by
      rw [add_sub_cancel_left, mul_comm]
      exact WittVector.mul_pow_charP_coeff_zero _ hm)
  exact h k hk

/- English proof (translation)
Introduce `p _ S K _ _ _ _ _ _ _ _ _ _ d U Y hY i`. Establish `hc : ∀ k, ∃ s : S, algebraMap S K s = (Y i).coeff k`. Introduce `k`. Take `⟨B, Z, Yn, h1, -⟩` from `digits p S K d U Y hY (k + 1)`. Use `⟨(B i).coeff k, ?_⟩` and prove the remaining obligations.

Rewrite using `[h1 i, coeff_add_p_pow_mul_lt p (k + 1) k (Nat.lt_succ_self k), WittVector.map_coeff]`. Use `choose c hc using hc`. Use `⟨WittVector.mk p c, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Rewrite using `[WittVector.map_coeff]`.

Conclude with `hc k`.
-/
theorem range_of_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Y : Fin d → WittVector p K), (∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i) → ∀ i, Y i ∈ (WittVector.map (p := p) (algebraMap S K)).range := by
  intro p _ S K _ _ _ _ _ _ _ _ _ _ d U Y hY i
  have hc : ∀ k, ∃ s : S, algebraMap S K s = (Y i).coeff k := by
    intro k
    obtain ⟨B, Z, Yn, h1, -⟩ := digits p S K d U Y hY (k + 1)
    refine ⟨(B i).coeff k, ?_⟩
    rw [h1 i, coeff_add_p_pow_mul_lt p (k + 1) k (Nat.lt_succ_self k), WittVector.map_coeff]
  choose c hc using hc
  refine ⟨WittVector.mk p c, ?_⟩
  ext k
  rw [WittVector.map_coeff]
  exact hc k

end GlobalTheory.LemY
