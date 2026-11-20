import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Introduce `K Kt _ _ p hp _ π ι F f h s A g hF hH hL`. Take `⟨z, hz, hw⟩` from `hL`. Establish `hp0 : p ≠ 0` using `hp.out.ne_zero`. Establish `hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0`. Rewrite using `[Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]`.

Establish `e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1` using `fun hg => by`. Rewrite using `[← mul_pow, inv_mul_cancel₀ hg, one_pow]`. Use `⟨fun i hi => ?_, fun i hi j hj => ?_⟩` and prove the remaining obligations. Take `⟨w, hwA, hFw⟩` from `hw i hi`. Use `⟨π w, hwA, fun hg => ?_⟩` and prove the remaining obligations.

Establish `key` using `(hF i).2 z (z ^ p * w) (by rw [hFw]; ring)`. Rewrite `key` using `[map_mul, map_pow, hz]`. Establish `e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹`. Take `⟨n, hn⟩ : ∃ n, p = n + 1` from `⟨p - 1, by omega⟩`. Rewrite using `[hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg, one_pow, mul_one]`.

Rewrite using `[(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1, e2 hg, one_smul]`. Take `⟨wi, hwiA, hFi⟩` from `hw i hi`. Take `⟨wj, hwjA, hFj⟩` from `hw j hj`. Establish `key` using `(hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)`. Rewrite `key` using `[map_mul, map_pow, map_sub, hz]`.

Rewrite using `[(hH i j).1, key]`. Distinguish the cases in `hg : g = 0`. Substitute `hg` using the available equality. Simplify using `[hp0]`. Rewrite using `[← mul_assoc, e2 hg, one_mul]`.

Conclude with `A.sub_mem hwjA hwiA`.
-/
theorem divided_frob_logForm : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by
  intro K Kt _ _ p hp _ π ι F f h s A g hF hH hL
  obtain ⟨z, hz, hw⟩ := hL
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1 := fun hg => by
    rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨w, hwA, hFw⟩ := hw i hi
    refine ⟨π w, hwA, fun hg => ?_⟩
    have key := (hF i).2 z (z ^ p * w) (by rw [hFw]; ring)
    rw [map_mul, map_pow, hz] at key
    have e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg,
        one_pow, mul_one]
    rw [(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1,
      e2 hg, one_smul]
  · obtain ⟨wi, hwiA, hFi⟩ := hw i hi
    obtain ⟨wj, hwjA, hFj⟩ := hw j hj
    have key := (hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)
    rw [map_mul, map_pow, map_sub, hz] at key
    rw [(hH i j).1, key]
    by_cases hg : g = 0
    · subst hg
      simp [hp0]
    · rw [← mul_assoc, e2 hg, one_mul]
      exact A.sub_mem hwjA hwiA

end GlobalTheory.DI
