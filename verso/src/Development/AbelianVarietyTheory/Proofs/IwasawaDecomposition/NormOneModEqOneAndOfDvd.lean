import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

namespace GlobalTheory.Mem.An

/- English proof (translation)
Introduce `d M p hd h`. Take `⟨A, B, hAB, hB, hA⟩` from `h`. Use `⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB, (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `hB`. Take `⟨k, hk⟩` from `hA`.

Establish `hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3` using `by omega`. Establish `hA' : A = 2 + M * b + 2 * M * k` using `by linear_combination hk`. Establish `key : (4 : ℤ) * (p - 1) = 4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)))`. Rewrite `hAB` using `[hA', hdq]`. Take the linear combination `-hAB`.

Establish `key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm`.
-/
theorem _root_.GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by
  intro d M p hd h
  obtain ⟨A, B, hAB, hB, hA⟩ := h
  refine ⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB,
    (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨k, hk⟩ := hA
  have hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3 := by omega
  have hA' : A = 2 + M * b + 2 * M * k := by linear_combination hk
  have key : (4 : ℤ) * (p - 1) =
      4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))) := by
    rw [hA', hdq] at hAB
    linear_combination -hAB
  have key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)) := by
    linarith
  exact (Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm

end GlobalTheory.Mem.An
