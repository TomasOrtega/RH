import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff

open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Use `haveI : NeZero r.den := ⟨r.den_nz⟩`. Use `haveI : NeZero (r.den : Ω) := ⟨Nat.cast_ne_zero.2 r.den_nz⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω r.den`.

Establish `hζ' : IsPrimitiveRoot (ε ζ) r.den` using `hζ.map_of_injective ε.injective`. Establish `he : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^ r.den = 1`. Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨r.num, ?_⟩` and prove the remaining obligations. Establish `h1 : ((r.den : ℚ) * r : ℚ) = r.num` using `Rat.den_mul_eq_num r`.

Establish `h2 : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ)` using `by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) h1`. Rewrite using `[← h2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one he`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.
-/
theorem exp_two_pi_rat_mem_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (r : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero r.den := ⟨r.den_nz⟩
  haveI : NeZero (r.den : Ω) := ⟨Nat.cast_ne_zero.2 r.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω r.den
  have hζ' : IsPrimitiveRoot (ε ζ) r.den := hζ.map_of_injective ε.injective
  have he : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^ r.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have h1 : ((r.den : ℚ) * r : ℚ) = r.num := Rat.den_mul_eq_num r
    have h2 : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) h1
    rw [← h2]; ring
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one he
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/- English proof (translation)
Establish `e : ∀ (γ : SL(2, ℤ)) (i j : Fin 2), ent (ofSL γ) i j = ((γ.1 i j : ℤ) : ℚ)` using `fun _ _ _ => rfl`. Establish `e10 : ent (ofSL ModularGroup.T) 1 0 = 0` using `by rw [e]; simp [ModularGroup.T]`. Establish `e00 : ent (ofSL ModularGroup.T) 0 0 = 1` using `by rw [e]; simp [ModularGroup.T]`. Establish `e01 : ent (ofSL ModularGroup.T) 0 1 = 1` using `by rw [e]; simp [ModularGroup.T]`. Establish `e11 : ent (ofSL ModularGroup.T) 1 1 = 1` using `by rw [e]; simp [ModularGroup.T]`.

Establish `key` using `X.exp_upper _ e10 h r`. Rewrite `key` using `[hh, e00, e01, e11, mul_one, div_one]`. Establish `h1 : eOm ε r = 1`. Establish `: eOm ε r * (X.exp h).coeff r = 1 * (X.exp h).coeff r` using `by rw [one_mul]; exact key.symm`. Conclude with `mul_right_cancel₀ hr this`.

Establish `h2 : ε (eOm ε r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))` using `Function.invFun_eq (exp_two_pi_rat_mem_range ε r)`. Rewrite `h2` using `[h1, map_one]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h2.symm`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h3 : (r : ℂ) = (n : ℂ)`.

Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions.
-/
theorem Tower.exponent_integral_of_translation_invariant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (hh : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  have e : ∀ (γ : SL(2, ℤ)) (i j : Fin 2), ent (ofSL γ) i j = ((γ.1 i j : ℤ) : ℚ) := fun _ _ _ => rfl
  have e10 : ent (ofSL ModularGroup.T) 1 0 = 0 := by rw [e]; simp [ModularGroup.T]
  have e00 : ent (ofSL ModularGroup.T) 0 0 = 1 := by rw [e]; simp [ModularGroup.T]
  have e01 : ent (ofSL ModularGroup.T) 0 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have e11 : ent (ofSL ModularGroup.T) 1 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have key := X.exp_upper _ e10 h r
  rw [hh, e00, e01, e11, mul_one, div_one] at key
  have h1 : eOm ε r = 1 := by
    have : eOm ε r * (X.exp h).coeff r = 1 * (X.exp h).coeff r := by rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hr this
  have h2 : ε (eOm ε r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) :=
    Function.invFun_eq (exp_two_pi_rat_mem_range ε r)
  rw [h1, map_one] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2.symm
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = (n : ℂ) := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

end GlobalTheory.KZ
