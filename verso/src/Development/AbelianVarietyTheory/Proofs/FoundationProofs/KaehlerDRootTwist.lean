import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5

namespace GlobalTheory.K5

/- English proof (translation)
Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `hzi : (ζ : S) * ((ζ⁻¹ : Sˣ) : S) = 1` using `Units.mul_inv ζ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S]`.

Simplify using `only [smul_add, smul_smul]`. Use `congr 2`. Establish `hw : ((ζ : S) ^ a) ^ (M + 1) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Rewrite using `[mul_pow]`.

Take the linear combination `r ^ M * hw`. Break down `a with _ | b` into its components or cases. Simplify using the standard rewrite rules. Establish `hw : ((ζ : S) ^ (b + 1)) ^ (M + 1) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`.

Simplify using `only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]`. Take the linear combination `((b : S) + 1) * r ^ (M + 1) * (((ζ⁻¹ : Sˣ) : S) * hw - ((ζ : S) ^ (b + 1)) ^ M * (ζ : S) ^ b * hzi)`. Rewrite using `[Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, Nat.add_sub_cancel]`.
-/
theorem kaehlerD_root_twist (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (ζ : Sˣ) (r : S)
    (N a : ℕ) (hN : 1 ≤ N) (hζ : (ζ : S) ^ N = 1) :
    ((ζ : S) ^ a * r) ^ (N - 1) • KaehlerDifferential.D R S ((ζ : S) ^ a * r) =
      r ^ (N - 1) • KaehlerDifferential.D R S r +
        ((a : S) * r ^ N * ((ζ⁻¹ : Sˣ) : S)) • KaehlerDifferential.D R S (ζ : S) ∧
    (N : S) • (r ^ (N - 1) • KaehlerDifferential.D R S r) = KaehlerDifferential.D R S (r ^ N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hzi : (ζ : S) * ((ζ⁻¹ : Sˣ) : S) = 1 := Units.mul_inv ζ
  constructor
  · rw [Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S]
    simp only [smul_add, smul_smul]
    congr 2
    · have hw : ((ζ : S) ^ a) ^ (M + 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
      rw [mul_pow]
      linear_combination r ^ M * hw
    · rcases a with _ | b
      · simp
      · have hw : ((ζ : S) ^ (b + 1)) ^ (M + 1) = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        linear_combination ((b : S) + 1) * r ^ (M + 1) *
          (((ζ⁻¹ : Sˣ) : S) * hw - ((ζ : S) ^ (b + 1)) ^ M * (ζ : S) ^ b * hzi)
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, Nat.add_sub_cancel]

end GlobalTheory.K5
