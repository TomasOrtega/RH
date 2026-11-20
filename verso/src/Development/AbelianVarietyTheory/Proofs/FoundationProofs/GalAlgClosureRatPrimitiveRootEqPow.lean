import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ _ _ s q hq`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero q := ⟨hq.ne'⟩`. Use `haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩`.

Take `⟨ζ₀, hζ₀⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω) (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')`. Establish `h0 : IsPrimitiveRoot ζ₀ q` using `(Polynomial.isRoot_cyclotomic_iff).mp hζ₀`. Establish `h1 : IsPrimitiveRoot (s ζ₀) q` using `h0.map_of_injective s.injective`. Take `⟨i, -, hi⟩` from `h0.eq_pow_of_pow_eq_one h1.pow_eq_one`. Establish `hcop : i.Coprime q` using `(h0.pow_iff_coprime hq i).mp (hi ▸ h1)`.

Use `⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩` and prove the remaining obligations. Introduce `ζ hζ`. Take `⟨k, -, hk⟩` from `h0.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Substitute `hk` using the available equality. Rewrite using `[zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem algEquiv_primitiveRoot_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q →
      ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  intro Ω _ _ _ s q hq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')
  have h0 : IsPrimitiveRoot ζ₀ q := (Polynomial.isRoot_cyclotomic_iff).mp hζ₀
  have h1 : IsPrimitiveRoot (s ζ₀) q := h0.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime q := (h0.pow_iff_coprime hq i).mp (hi ▸ h1)
  refine ⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩
  intro ζ hζ
  obtain ⟨k, -, hk⟩ := h0.eq_pow_of_pow_eq_one hζ.pow_eq_one
  subst hk
  rw [zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory
