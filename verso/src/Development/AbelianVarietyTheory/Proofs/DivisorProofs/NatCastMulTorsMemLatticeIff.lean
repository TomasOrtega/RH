import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

/- English proof (translation)
Rewrite using `[← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]`.
-/
theorem nsmul_zmod_eq_zero_iff_dvd (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]

/- English proof (translation)
Introduce `N _ τ M x`. Establish `hN : (N : ℂ) ≠ 0` using `by exact_mod_cast NeZero.ne N`. Establish `hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val`. Rewrite using `[← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]`. Both sides reduce to the same expression.

Establish `hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z`. Introduce `z`. Rewrite using `[PeriodPair.mem_lattice]`. Simplify using `[tauPair]`. Rewrite using `[hx, hm]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, h⟩`. Establish `h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0`. Unfold `tors at h`. Clear denominators, using `at h` for the nonvanishing conditions.

Use `push_cast`. Take the linear combination `h`. Establish `him` using `congrArg Complex.im h1`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him`. Rewrite `h1` using `[him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← Int.natCast_dvd_natCast]`. Conclude with `⟨m, by push_cast at him ⊢; linear_combination -him⟩`. Rewrite using `[← Int.natCast_dvd_natCast]`. Conclude with `⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩`.

Introduce and unpack `⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩`. Use `⟨m, n, ?_⟩` and prove the remaining obligations. Establish `a : (M : ℂ) * ((x 0).val : ℂ) = N * m` using `by exact_mod_cast hm0`. Establish `b : (M : ℂ) * ((x 1).val : ℂ) = N * n` using `by exact_mod_cast hn0`. Unfold `tors`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Take the linear combination `-(τ : ℂ) * a - b`.
-/
theorem natCast_mul_tors_mem_lattice_iff :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by
  intro N _ τ M x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val := by
    rw [← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]
    rfl
  have hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z := by
    intro z
    rw [PeriodPair.mem_lattice]; simp [tauPair]
  rw [hx, hm]
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0 := by
      unfold tors at h
      field_simp at h
      push_cast
      linear_combination h
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him
    rw [him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h1
    constructor
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨m, by push_cast at him ⊢; linear_combination -him⟩
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩
  · rintro ⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩
    refine ⟨m, n, ?_⟩
    have a : (M : ℂ) * ((x 0).val : ℂ) = N * m := by exact_mod_cast hm0
    have b : (M : ℂ) * ((x 1).val : ℂ) = N * n := by exact_mod_cast hn0
    unfold tors
    field_simp
    push_cast
    linear_combination -(τ : ℂ) * a - b

end GlobalTheory.WpFam
