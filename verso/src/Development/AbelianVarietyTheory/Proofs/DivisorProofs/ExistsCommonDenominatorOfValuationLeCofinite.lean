import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.ValBoundDenom

/- English proof (translation)
Proceed by induction on `a using WithZero.recZeroCoe with`. Consider the case `zero => exact ⟨0, zero_le'⟩`. Consider the case `coe m`. Use `⟨(Multiplicative.toAdd m).toNat, ?_⟩` and prove the remaining obligations. Use `show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Rewrite using `[WithZero.coe_le_coe]`. Conclude with `Int.self_le_toNat (Multiplicative.toAdd m)`.
-/
theorem exists_nat_le_exp (a : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, a ≤ WithZero.exp (n : ℤ) := by
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    exact Int.self_le_toNat (Multiplicative.toAdd m)

/- English proof (translation)
Establish `hfin : {w | ¬ β w ≤ 1}.Finite` using `Filter.eventually_cofinite.mp hβ`. Use `set T := hfin.toFinset with hT`. Use `choose k hk using fun w => exists_nat_le_exp (β w)`. Use `set I : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal ^ k w with hI`. Establish `hI0 : I ≠ ⊥`.

Rewrite using `[hI, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Introduce `w _`. Conclude with `pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)`. Take `⟨D, hDI, hD0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI0`. Use `⟨D, hD0, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hle : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E ((D : E) * x) ≤ 1`. Introduce `w`. Rewrite using `[map_mul]`. Distinguish the cases in `hw : w ∈ T`. Establish `hmem : D ∈ w.asIdeal ^ k w` using `(Finset.inf_le hw : T.inf (fun w => w.asIdeal ^ k w) ≤ _) (Ideal.prod_le_inf hDI)`.

Establish `h1 : w.valuation E (D : E) ≤ WithZero.exp (-(k w : ℤ))`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hmem`. Establish `h2 : w.valuation E x ≤ WithZero.exp (k w : ℤ)` using `(hx w).trans (hk w)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hw1 : β w ≤ 1`. Assume the negation of the conclusion as `h`. Conclude with `hw (by rw [hT, Set.Finite.mem_toFinset]; exact h)`. Conclude with `mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ((hx w).trans hw1)`. Take `⟨r, hr⟩` from `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hle`.

Rewrite using `[← hr]`. Conclude with `r.isIntegral_coe`.
-/
theorem exists_common_denominator_of_valuation_le (E : Type) [Field E] [NumberField E]
    (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ))
    (hβ : ∀ᶠ w in Filter.cofinite, β w ≤ 1) : ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) →
        IsIntegral ℤ ((D : E) * x) := by
  classical
  have hfin : {w | ¬ β w ≤ 1}.Finite := Filter.eventually_cofinite.mp hβ
  set T := hfin.toFinset with hT
  choose k hk using fun w => exists_nat_le_exp (β w)
  set I : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal ^ k w with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro w _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨D, hDI, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  refine ⟨D, hD0, fun x hx => ?_⟩
  have hle : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E ((D : E) * x) ≤ 1 := by
    intro w
    rw [map_mul]
    by_cases hw : w ∈ T
    · have hmem : D ∈ w.asIdeal ^ k w :=
        (Finset.inf_le hw : T.inf (fun w => w.asIdeal ^ k w) ≤ _) (Ideal.prod_le_inf hDI)
      have h1 : w.valuation E (D : E) ≤ WithZero.exp (-(k w : ℤ)) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hmem
      have h2 : w.valuation E x ≤ WithZero.exp (k w : ℤ) := (hx w).trans (hk w)
      calc w.valuation E (D : E) * w.valuation E x
          ≤ WithZero.exp (-(k w : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' h1 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have hw1 : β w ≤ 1 := by
        by_contra h
        exact hw (by rw [hT, Set.Finite.mem_toFinset]; exact h)
      exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ((hx w).trans hw1)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hle
  rw [← hr]
  exact r.isIntegral_coe

end GlobalTheory.ValBoundDenom
