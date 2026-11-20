import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.JStab

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hε : Function.Injective ε` using `ε.injective`. Unfold `eOm`. Apply `Function.invFun_eq` to reduce the goal to its premises.

Use `haveI : NeZero (x.den : Ω) := ⟨by exact_mod_cast x.den_nz⟩`. Take `⟨ζ, hζ0⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω) (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 x.den_pos).ne')`. Establish `hζ : IsPrimitiveRoot ζ x.den` using `(Polynomial.isRoot_cyclotomic_iff).1 hζ0`. Establish `hζ' : IsPrimitiveRoot (ε ζ) x.den` using `hζ.map_of_injective hε`. Use `haveI : NeZero x.den := ⟨x.den_nz⟩`.

Establish `hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1`. Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨x.num, ?_⟩` and prove the remaining obligations. Establish `hx : (x : ℂ) * x.den = x.num` using `by exact_mod_cast Rat.mul_den_eq_num x`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one hpow`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.
-/
theorem eps_eOm_of_alg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  haveI : NeZero (x.den : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  obtain ⟨ζ, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 x.den_pos).ne')
  have hζ : IsPrimitiveRoot ζ x.den := (Polynomial.isRoot_cyclotomic_iff).1 hζ0
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/- English proof (translation)
Introduce `h0`. Use `eps_eOm_of_alg ε x` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `Complex.exp_ne_zero _ this.symm`.
-/
theorem eOm_ne_zero' {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x ≠ 0 := by
  intro h0
  have := eps_eOm_of_alg ε x
  rw [h0, map_zero] at this
  exact Complex.exp_ne_zero _ this.symm

end GlobalTheory.KZ.ES.JStab
