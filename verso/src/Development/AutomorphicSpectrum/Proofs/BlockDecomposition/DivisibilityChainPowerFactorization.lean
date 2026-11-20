import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NormalForm

/- English proof (translation)
Introduce `S _ ϖ hd f M`. Proceed by induction on `M generalizing f with`. Consider the case `zero => exact Or.inl (by simp)`. Consider the case `succ M ih`. Break down `hd f with ⟨g, rfl⟩ | hf` into its components or cases.

Break down `ih g with hg | ⟨j, f', hg, hf'⟩` into its components or cases. Use `left`. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left ϖ hg`. Use `right`.

Use `⟨j + 1, f', ?_, hf'⟩` and prove the remaining obligations. Rewrite using `[hg, pow_succ', mul_assoc]`. Conclude with `Or.inr ⟨0, f, by simp, hf⟩`.
-/
theorem normal_form_of_dichotomy :
    ∀ {S : Type} [CommRing S] (ϖ : S), (∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) →
      ∀ (f : S) (M : ℕ), ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  intro S _ ϖ hd f M
  induction M generalizing f with
  | zero => exact Or.inl (by simp)
  | succ M ih =>
    rcases hd f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', hg, hf'⟩
      · left
        rw [pow_succ']
        exact mul_dvd_mul_left ϖ hg
      · right
        refine ⟨j + 1, f', ?_, hf'⟩
        rw [hg, pow_succ', mul_assoc]
    · exact Or.inr ⟨0, f, by simp, hf⟩

end GlobalTheory.CompanionTheory.NormalForm
