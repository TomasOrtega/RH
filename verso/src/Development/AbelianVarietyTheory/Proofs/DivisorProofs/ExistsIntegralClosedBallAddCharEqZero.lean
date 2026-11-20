import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ lam _ ψ _ _ hne`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (by ext x; simpa using h x)`.

Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `ht (by simp)`. Use `⟨Units.mk0 t ht0, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hs' : t ∈ GlobalTheory.SplitWeil.cball s` using `hs`.

Establish `hm : MeasurableSet (GlobalTheory.SplitWeil.cball s)` using `(GlobalTheory.SplitWeil.isOpen_cball s).measurableSet`. Establish `hadd : ∀ x y : F, x ∈ GlobalTheory.SplitWeil.cball s → y ∈ GlobalTheory.SplitWeil.cball s → x + y ∈ GlobalTheory.SplitWeil.cball s` using `fun x y hx hy => by`. Simplify using `only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx hy ⊢`. Conclude with `Valuation.map_add_le _ hx hy`. Establish `hneg : -t ∈ GlobalTheory.SplitWeil.cball s`.

Simplify `hs'` using `[GlobalTheory.SplitWeil.cball]`. Establish `hiff : ∀ x : F, t + x ∈ GlobalTheory.SplitWeil.cball s ↔ x ∈ GlobalTheory.SplitWeil.cball s` using `fun x => ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩`. Rewrite using `[← integral_indicator hm]`. Establish `h1` using `integral_add_left_eq_self (μ := lam) ((GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x)) t`. Establish `h2 : (fun x => (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) (t + x)) = fun x => ψ t * (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ GlobalTheory.SplitWeil.cball s`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)), mul_zero]`. Rewrite `h1` using `[h2, integral_const_mul]`.

Establish `h3 : (ψ t - 1) * ∫ x, (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x ∂lam = 0`. Rewrite using `[sub_mul, h1, one_mul, sub_self]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)`.
-/
theorem exists_integral_cball_char_eq_zero :
    ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  intro F _ _ _ _ _ _ _ lam _ ψ _ _ hne
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext x; simpa using h x)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by simp)
  refine ⟨Units.mk0 t ht0, fun s hs => ?_⟩
  have hs' : t ∈ GlobalTheory.SplitWeil.cball s := hs
  have hm : MeasurableSet (GlobalTheory.SplitWeil.cball s) := (GlobalTheory.SplitWeil.isOpen_cball s).measurableSet
  have hadd : ∀ x y : F, x ∈ GlobalTheory.SplitWeil.cball s → y ∈ GlobalTheory.SplitWeil.cball s →
      x + y ∈ GlobalTheory.SplitWeil.cball s := fun x y hx hy => by
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  have hneg : -t ∈ GlobalTheory.SplitWeil.cball s := by
    simpa [GlobalTheory.SplitWeil.cball] using hs'
  have hiff : ∀ x : F, t + x ∈ GlobalTheory.SplitWeil.cball s ↔ x ∈ GlobalTheory.SplitWeil.cball s := fun x =>
    ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩
  rw [← integral_indicator hm]
  have h1 := integral_add_left_eq_self (μ := lam)
    ((GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x)) t
  have h2 : (fun x => (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) (t + x))
      = fun x => ψ t * (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x := by
    funext x
    by_cases hx : x ∈ GlobalTheory.SplitWeil.cball s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)), mul_zero]
  rw [h2, integral_const_mul] at h1
  have h3 : (ψ t - 1) * ∫ x, (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x ∂lam = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)

end GlobalTheory.KSp
