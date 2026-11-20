import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance`. Use `set n := x.den with hn`. Establish `hn0 : 0 < n` using `x.den_pos`. Use `haveI : NeZero n := ⟨hn0.ne'⟩`.

Use `haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω) (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'`. Establish `hp : IsPrimitiveRoot ζ n` using `(Polynomial.isRoot_cyclotomic_iff).mp hζ`. Establish `hp' : IsPrimitiveRoot (ε ζ) n` using `hp.map_of_injective hε`. Establish `hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1`.

Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨x.num, ?_⟩` and prove the remaining obligations. Establish `h` using `Rat.mul_den_eq_num x`. Establish `h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ)` using `by exact_mod_cast h`. Rewrite using `[← h']`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨i, -, hi⟩` from `hp'.eq_pow_of_pow_eq_one hpow`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.
-/
theorem exists_eq_exp_of_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  set n := x.den with hn
  have hn0 : 0 < n := x.den_pos
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'
  have hp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hp' : IsPrimitiveRoot (ε ζ) n := hp.map_of_injective hε
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have h := Rat.mul_den_eq_num x
    have h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ) := by exact_mod_cast h
    rw [← h']; ring
  obtain ⟨i, -, hi⟩ := hp'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/- English proof (translation)
The claim follows from `Function.invFun_eq (exists_eq_exp_of_rat ε hε x)`.
-/
theorem eOm_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_eq_exp_of_rat ε hε x)

/- English proof (translation)
Introduce `Ω _ _ _ ε hε`. Use `⟨eOm_spec ε hε, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Apply `hε` to reduce the goal to its premises. Rewrite using `[map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `k`. Apply `hε` to reduce the goal to its premises.

Rewrite using `[map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]`. Conclude with `⟨k, by push_cast; ring⟩`. Introduce `x hx`. Establish `h` using `eOm_spec ε hε x`. Rewrite `h` using `[hx, map_one]`.

Take `⟨k, hk⟩` from `Complex.exp_eq_one_iff.mp h.symm`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `: (x : ℂ) = (k : ℂ)`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.
-/
theorem eOm_props : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε → (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ k : ℤ, eOm ε (k : ℚ) = 1) ∧ (∀ x : ℚ, eOm ε x = 1 → ∃ k : ℤ, x = k) := by
  intro Ω _ _ _ ε hε
  refine ⟨eOm_spec ε hε, ?_, ?_, ?_⟩
  · intro x y
    apply hε
    rw [map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]
    congr 1; push_cast; ring
  · intro k
    apply hε
    rw [map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  · intro x hx
    have h := eOm_spec ε hε x
    rw [hx, map_one] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
    refine ⟨k, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      rw [hk]; ring
    exact_mod_cast this

end GlobalTheory.KZ
