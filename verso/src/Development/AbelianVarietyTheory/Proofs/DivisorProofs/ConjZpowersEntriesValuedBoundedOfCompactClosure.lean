import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PowBdd

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨c, hc⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hc.symm`.

Establish `: {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]`. Rewrite using `[this]`. Conclude with `Valued.isOpen_closedBall _ (by simp [hc0])`.
-/
theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

/- English proof (translation)
Take `⟨s, hs⟩` from `hC.elim_finite_subcover (fun m : ℤ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m}) (fun m => isOpen_le_exp w m) (by`. Introduce `x _`. Rewrite using `[Set.mem_iUnion]`. Distinguish the cases in `h0 : Valued.v x = 0`. Conclude with `⟨0, by simp [h0]⟩`.

Conclude with `⟨WithZero.log (Valued.v x), by simp [WithZero.exp_log h0]⟩)`. Use `⟨s.sup fun m => WithZero.exp m, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, hxm⟩` from `Set.mem_iUnion₂.1 (hs hx)`. Conclude with `hxm.trans (Finset.le_sup (f := fun m => WithZero.exp m) hm)`.
-/
theorem exists_bound_of_isCompact (w : Pl E) {C : Set (w.adicCompletion E)} (hC : IsCompact C) :
    ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v x ≤ B := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun m : ℤ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m})
    (fun m => isOpen_le_exp w m) (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases h0 : Valued.v x = 0
      · exact ⟨0, by simp [h0]⟩
      · exact ⟨WithZero.log (Valued.v x), by simp [WithZero.exp_log h0]⟩)
  refine ⟨s.sup fun m => WithZero.exp m, fun x hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact hxm.trans (Finset.le_sup (f := fun m => WithZero.exp m) hm)

end GlobalTheory.PowBdd

open GlobalTheory.PowBdd in
/- English proof (translation)
Introduce `E _ _ _ n w t g hc`. Establish `hent : ∀ i j : Fin n, ∃ B : WithZero (Multiplicative ℤ), ∀ k : ℤ, Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B`. Introduce `i j`. Set `f : UL n w → w.adicCompletion E` to `fun y => (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j`. Establish `hf : Continuous f`.

Establish `h1 : Continuous fun y : UL n w => (g⁻¹ * y * g : UL n w)` using `(continuous_const.mul continuous_id).mul continuous_const`. Establish `h2 : Continuous fun y : UL n w => (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))` using `Units.continuous_val.comp (continuous_subtype_val.comp h1)`. Conclude with `(continuous_apply j).comp ((continuous_apply i).comp h2)`. Take `⟨B, hB⟩` from `exists_bound_of_isCompact w (hc.image hf)`. Use `⟨B, fun k => hB _ ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), rfl⟩⟩` and prove the remaining obligations.

Use `choose B hB using hent`. Use `⟨Finset.univ.sup fun p : Fin n × Fin n => B p.1 p.2, fun k i j => ?_⟩` and prove the remaining obligations. Conclude with `(hB i j k).trans (Finset.le_sup (f := fun p : Fin n × Fin n => B p.1 p.2) (Finset.mem_univ (i, j)))`.
-/
theorem GlobalTheory.BCT.powers_entries_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  intro E _ _ _ n w t g hc
  have hent : ∀ i j : Fin n, ∃ B : WithZero (Multiplicative ℤ), ∀ k : ℤ,
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
    intro i j
    let f : UL n w → w.adicCompletion E := fun y =>
      (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
    have hf : Continuous f := by
      have h1 : Continuous fun y : UL n w => (g⁻¹ * y * g : UL n w) :=
        (continuous_const.mul continuous_id).mul continuous_const
      have h2 : Continuous fun y : UL n w => (((g⁻¹ * y * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
        Units.continuous_val.comp (continuous_subtype_val.comp h1)
      exact (continuous_apply j).comp ((continuous_apply i).comp h2)
    obtain ⟨B, hB⟩ := exists_bound_of_isCompact w (hc.image hf)
    refine ⟨B, fun k => hB _ ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), rfl⟩⟩
  choose B hB using hent
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => B p.1 p.2, fun k i j => ?_⟩
  exact (hB i j k).trans (Finset.le_sup (f := fun p : Fin n × Fin n => B p.1 p.2) (Finset.mem_univ (i, j)))
