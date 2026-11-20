import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra k K := φ.toAlgebra`. Establish `h1 : IsAlgebraic k f` using `⟨P, hP, hf⟩`. Establish `h2 : IsAlgebraic k (f - φ c)` using `h1.sub (isAlgebraic_algebraMap c)`. Use `haveI : Valuation.IsTrivialOn k (AddValuation.toValuation v) := ⟨fun a ha => hv a ha⟩`. Assume the negation of the conclusion as `hne`.

Conclude with `Valuation.transcendental_of_ne_one k (v := AddValuation.toValuation v) _ h hne h2`.
-/
theorem addVal_eq_zero_of_root_sub_const {k K : Type} [Field k] [Field K] (φ : k →+* K)
    (v : AddValuation K (WithTop ℤ)) (hv : ∀ a : k, a ≠ 0 → v (φ a) = 0) (f : K) (P : k[X])
    (hP : P ≠ 0) (hf : eval₂ φ f P = 0) (c : k) (h : f - φ c ≠ 0) : v (f - φ c) = 0 := by
  letI : Algebra k K := φ.toAlgebra
  have h1 : IsAlgebraic k f := ⟨P, hP, hf⟩
  have h2 : IsAlgebraic k (f - φ c) := h1.sub (isAlgebraic_algebraMap c)
  haveI : Valuation.IsTrivialOn k (AddValuation.toValuation v) := ⟨fun a ha => hv a ha⟩
  by_contra hne
  exact Valuation.transcendental_of_ne_one k (v := AddValuation.toValuation v) _ h hne h2

/- English proof (translation)
Introduce and unpack `k _ f ⟨P, hP, hf⟩`. Use `⟨f.coeff 0, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h : f - HahnSeries.C (f.coeff 0) ≠ 0` using `sub_ne_zero.2 hne`. Establish `h0` using `addVal_eq_zero_of_root_sub_const (K := LaurentSeries k) HahnSeries.C (HahnSeries.addVal ℤ k) (fun a ha => by`.

Rewrite using `[HahnSeries.addVal_apply_of_ne (HahnSeries.C_ne_zero ha), HahnSeries.order_C]`. Use the proof step `rfl)`. Use `f P hP hf _ h`. Rewrite `h0` using `[HahnSeries.addVal_apply]`. Establish `h1` using `HahnSeries.coeff_orderTop_ne (g := 0) h0`.

Apply `h1` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem laurentSeries_eq_C_of_root : ∀ (k : Type) [Field k] (f : LaurentSeries k),
    (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  rintro k _ f ⟨P, hP, hf⟩
  refine ⟨f.coeff 0, ?_⟩
  by_contra hne
  have h : f - HahnSeries.C (f.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have h0 := addVal_eq_zero_of_root_sub_const (K := LaurentSeries k) HahnSeries.C
    (HahnSeries.addVal ℤ k) (fun a ha => by
      rw [HahnSeries.addVal_apply_of_ne (HahnSeries.C_ne_zero ha), HahnSeries.order_C]; rfl)
    f P hP hf _ h
  rw [HahnSeries.addVal_apply] at h0
  have h1 := HahnSeries.coeff_orderTop_ne (g := 0) h0
  apply h1
  simp

end GlobalTheory
