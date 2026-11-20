import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
open NumberField IsDedekindDomain

namespace GlobalTheory.CompletionIsom

open WithZero in

/- English proof (translation)
Establish `hπ0 : π ≠ 0` using `by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm`. Establish `hy0 : y₀ ≠ 0` using `by rintro rfl; rw [map_zero] at hy₀; exact exp_ne_zero hy₀.symm`. Establish `hexp : ∀ (w : Valuation K (WithZero (Multiplicative ℤ))) (x : K), x ≠ 0 → ∃ a : ℤ, w x = exp a` using `fun w x hx => ⟨_, (exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩`. Establish `hker : ∀ z, v z = 1 → v' z = 1`. Introduce `z hz`.

Establish `hz0 : z ≠ 0` using `by rintro rfl; rw [map_zero] at hz; exact zero_ne_one hz`. Take `⟨a, ha⟩` from `hexp v' z hz0`. Break down `lt_trichotomy a 0 with h1 | h1 | h1` into its components or cases. Use `(h z).2 (by rw [ha, ← exp_zero, exp_lt_exp]; exact h1)` as an intermediate fact. Rewrite `this` using `[hz]`.

Conclude with `absurd this (lt_irrefl _)`. Rewrite using `[ha, h1, exp_zero]`. Use `(h z⁻¹).2 (by rw [map_inv₀, ha, ← exp_neg, ← exp_zero, exp_lt_exp]; omega)` as an intermediate fact. Rewrite `this` using `[map_inv₀, hz, inv_one]`. Conclude with `absurd this (lt_irrefl _)`.

Take `⟨e, he⟩` from `hexp v' π hπ0`. Take `⟨b, hb⟩` from `hexp v y₀ hy0`. Establish `he1 : e < 0`. Use `(h π).1 (by rw [hπ, ← exp_zero, exp_lt_exp]; omega)` as an intermediate fact. Rewrite `this` using `[he, ← exp_zero, exp_lt_exp]`. Then use the resulting hypothesis.

Establish `hb1 : b < 0`. Use `(h y₀).2 (by rw [hy₀, ← exp_zero, exp_lt_exp]; omega)` as an intermediate fact. Rewrite `this` using `[hb, ← exp_zero, exp_lt_exp]`. Then use the resulting hypothesis. Establish `he2 : -1 ≤ e`. Assume the negation of the conclusion as `hc`.

Use `(h (π * y₀⁻¹)).2 (by` as an intermediate fact. Rewrite using `[map_mul, map_inv₀, he, hy₀, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]`. Use the proof step `omega)`. Rewrite `this` using `[map_mul, map_inv₀, hπ, hb, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `hπ' : v' π = exp (-1)` using `by rw [he]; congr 1; omega`. Introduce `y`. Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, map_zero, map_zero]`. Take `⟨a, ha⟩` from `hexp v y hy`.

Establish `hz` using `hker (y * π ^ a) (by`. Rewrite using `[map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, ← exp_zero]`. Use `congr 1`. Use the proof step `simp)`. Rewrite `hz` using `[map_mul, map_zpow₀, hπ', ← exp_zsmul]`.

Rewrite using `[ha, eq_inv_of_mul_eq_one_left hz, ← exp_neg]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem valuation_eq_of_lt_one_iff {K : Type} [Field K] (v v' : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ y, v y < 1 ↔ v' y < 1) (π : K) (hπ : v π = exp (-1)) (y₀ : K) (hy₀ : v' y₀ = exp (-1)) :
    ∀ y, v' y = v y := by
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hy0 : y₀ ≠ 0 := by rintro rfl; rw [map_zero] at hy₀; exact exp_ne_zero hy₀.symm
  have hexp : ∀ (w : Valuation K (WithZero (Multiplicative ℤ))) (x : K), x ≠ 0 → ∃ a : ℤ, w x = exp a :=
    fun w x hx => ⟨_, (exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩
  have hker : ∀ z, v z = 1 → v' z = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact zero_ne_one hz
    obtain ⟨a, ha⟩ := hexp v' z hz0
    rcases lt_trichotomy a 0 with h1 | h1 | h1
    · have := (h z).2 (by rw [ha, ← exp_zero, exp_lt_exp]; exact h1)
      rw [hz] at this; exact absurd this (lt_irrefl _)
    · rw [ha, h1, exp_zero]
    · have := (h z⁻¹).2 (by rw [map_inv₀, ha, ← exp_neg, ← exp_zero, exp_lt_exp]; omega)
      rw [map_inv₀, hz, inv_one] at this; exact absurd this (lt_irrefl _)
  obtain ⟨e, he⟩ := hexp v' π hπ0
  obtain ⟨b, hb⟩ := hexp v y₀ hy0
  have he1 : e < 0 := by
    have := (h π).1 (by rw [hπ, ← exp_zero, exp_lt_exp]; omega)
    rwa [he, ← exp_zero, exp_lt_exp] at this
  have hb1 : b < 0 := by
    have := (h y₀).2 (by rw [hy₀, ← exp_zero, exp_lt_exp]; omega)
    rwa [hb, ← exp_zero, exp_lt_exp] at this
  have he2 : -1 ≤ e := by
    by_contra hc
    have := (h (π * y₀⁻¹)).2 (by
      rw [map_mul, map_inv₀, he, hy₀, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]; omega)
    rw [map_mul, map_inv₀, hπ, hb, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp] at this
    omega
  have hπ' : v' π = exp (-1) := by rw [he]; congr 1; omega
  intro y
  by_cases hy : y = 0
  · rw [hy, map_zero, map_zero]
  obtain ⟨a, ha⟩ := hexp v y hy
  have hz := hker (y * π ^ a) (by
    rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, ← exp_zero]; congr 1; simp)
  rw [map_mul, map_zpow₀, hπ', ← exp_zsmul] at hz
  rw [ha, eq_inv_of_mul_eq_one_left hz, ← exp_neg]
  congr 1; simp

/- English proof (translation)
Introduce `E E' _ _ _ _ _ w w' i hi _ y`. Use `GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w` as an intermediate fact. Establish `ho : IsOpenMap i` using `AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi`. Establish `hi' : Continuous i.symm` using `i.toEquiv.continuous_symm_iff.2 ho`. Take `⟨π, hπ⟩` from `w.valuedAdicCompletion_surjective E (WithZero.exp (-1))`.

Take `⟨ϖ, hϖ⟩` from `w'.valuedAdicCompletion_surjective E' (WithZero.exp (-1))`. Use `valuation_eq_of_lt_one_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) ((Valued.v : Valuation (w'.adicCompletion E') (WithZero (Multiplicative ℤ))).comap i.toRingHom) (fun x => ⟨fun hx => GlobalTheory.ConjParahoric.val_lt_one_map i.toRingHom hi hx, f …` and prove the remaining obligations. Use `GlobalTheory.ConjParahoric.val_lt_one_map i.symm.toRingHom hi' hx` as an intermediate fact. Simplify using `using this`. Simplify using `using hϖ`.
-/
theorem valued_v_map : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  intro E E' _ _ _ _ _ w w' i hi _ y
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  have hi' : Continuous i.symm := i.toEquiv.continuous_symm_iff.2 ho
  obtain ⟨π, hπ⟩ := w.valuedAdicCompletion_surjective E (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := w'.valuedAdicCompletion_surjective E' (WithZero.exp (-1))
  refine valuation_eq_of_lt_one_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
    ((Valued.v : Valuation (w'.adicCompletion E') (WithZero (Multiplicative ℤ))).comap i.toRingHom)
    (fun x => ⟨fun hx => GlobalTheory.ConjParahoric.val_lt_one_map i.toRingHom hi hx, fun hx => ?_⟩) π hπ (i.symm ϖ) ?_ y
  · have := GlobalTheory.ConjParahoric.val_lt_one_map i.symm.toRingHom hi' hx
    simpa using this
  · simpa using hϖ

end GlobalTheory.CompletionIsom
