import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

/- English proof (translation)
Proceed by induction on `ss with`. Consider the case `nil`. Introduce `χ`. Conclude with `⟨0, by funext a; simp [pathEnd], by simp⟩`. Consider the case `cons s ss ih`.

Introduce `χ`. Take `⟨m', h, hm⟩` from `ih (χ + Pi.single s 1)`. Use `⟨m' + Pi.single s 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pathEnd, h]`. Use function extensionality and compare the values at `a`.

Distinguish the cases in `e : a = s`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Pi.single_eq_of_ne e]`.

Introduce `a ha`. Break down `List.mem_cons.1 ha with rfl | ha` into its components or cases. Simplify using the standard rewrite rules. Use `hm a ha` as an intermediate fact. Simplify using `only [Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    exact ⟨0, by funext a; simp [pathEnd], by simp⟩
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · rw [pathEnd, h]
      funext a
      by_cases e : a = s
      · subst e
        simp
        ring
      · simp [Pi.single_eq_of_ne e]
    · intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · simp
      · have := hm a ha
        simp only [Pi.add_apply]
        omega

/- English proof (translation)
Introduce `_ χ ss` and use `pathEnd_eq_add_nat ss χ`.
-/
theorem pathEndNat : CompanionTheory.RgExh.Fin.PathEndNat := fun _ χ ss => pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
