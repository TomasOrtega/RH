import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPowEqOneOfValuationSubLtOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameTau

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one`. Consider the case `exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one`. Consider the case `(apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one ..)`.
-/
theorem root_eq_of_close {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω}
    (h : ζ ^ m = 1) (h' : ζ' ^ m = 1) (hm : ¬ A.valuation (m : Ω) < 1)
    (hc : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  first
  | exact @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | (apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one ..)

/- English proof (translation)
Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`. Use `root_eq_of_close A m (by rw [← map_pow, hζ, map_one]) hζ hm ?_` and prove the remaining obligations. Conclude with `hσ.2 ζ (valuation_eq_one_of_pow_eq_one A hm0 hζ).le`.
-/
theorem ine_fix_root {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  refine root_eq_of_close A m (by rw [← map_pow, hζ, map_one]) hζ hm ?_
  exact hσ.2 ζ (valuation_eq_one_of_pow_eq_one A hm0 hζ).le

/- English proof (translation)
Establish `hτ : (τ π / π) ^ m = 1`. Rewrite using `[div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]`. Establish `hfix` using `ine_fix_root hσ m hm hτ`. Establish `e1 : τ π = (τ π / π) * π` using `by field_simp`. Establish `e2 : (σ * τ) π = σ (τ π / π) * σ π`.

Rewrite using `[AlgEquiv.mul_apply, ← map_mul, div_mul_cancel₀ _ hπ]`. Rewrite using `[e2, hfix]`. Clear the denominators using the available nonvanishing facts.
-/
theorem quot_mul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ τ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {π : Ω} (hπ : π ≠ 0)
    {e : E} (he : π ^ m = algebraMap E Ω e) :
    (σ * τ) π / π = (σ π / π) * (τ π / π) := by
  have hτ : (τ π / π) ^ m = 1 := by
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hfix := ine_fix_root hσ m hm hτ
  have e1 : τ π = (τ π / π) * π := by field_simp
  have e2 : (σ * τ) π = σ (τ π / π) * σ π := by
    rw [AlgEquiv.mul_apply, ← map_mul, div_mul_cancel₀ _ hπ]
  rw [e2, hfix]
  field_simp

end GlobalTheory.TameTau
