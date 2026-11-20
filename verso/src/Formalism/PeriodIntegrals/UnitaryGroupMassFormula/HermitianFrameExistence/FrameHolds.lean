import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer

noncomputable section

namespace PI.ScPiFrameW

open PI.ScPiExists

/- English proof (translation)
Introduce `I r k e f z hn hfr ⟨t, ht, hzz⟩ hε v`. Take `⟨hee, hff, hef, hz⟩` from `hfr`. Establish `hσ : ∃ σ : Fin (r + 1) → Fin I.n, ∀ i, I.ε v i = false → ∃ j, σ j = i`. Use `⟨fun j => ⟨min ((k - 1) + 2 * j.val + 1) (I.n - 1), by omega⟩, ?_⟩` and prove the remaining obligations. Introduce `i hi`.

Rewrite `hi` using `[hε v i]`. Establish `h2 : ¬ i.val < k - 1 ∧ (i.val - (k - 1)) % 2 ≠ 0`. Distinguish the cases in `h1 : i.val < k - 1`. Simplify using `[h1] at hi`. Simplify using `[h1] at hi`.

Conclude with `⟨h1, by omega⟩`. Establish `hi'` using `i.isLt`. Use `⟨⟨(i.val - (k - 1)) / 2, by omega⟩, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Use `show min ((k - 1) + 2 * ((i.val - (k - 1)) / 2) + 1) (I.n - 1) = i.val`.

Use linear arithmetic over natural numbers and integers. Take `⟨σ, hσ⟩` from `hσ`. Apply the tactic sequence `obtain ⟨w, hw1, hw2⟩ := frame_core (I.ε v) hn σ hσ (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) (t : ℝ) (by exact_mod_cast ht) (fun a b => by rw [hJ_rv, hee a b, map_zero]) (fun a b => by rw [hJ_rv, hff a b, map_zero]) (fun a b => by rw [hJ_rv, hef a b]; split_ifs < …`. Conclude with `⟨w, hw1, hw2⟩`.
-/
theorem frame_holds : PI.ScPiExists.Frame := by
  intro I r k e f z hn hfr ⟨t, ht, hzz⟩ hε v
  obtain ⟨hee, hff, hef, hz⟩ := hfr
  have hσ : ∃ σ : Fin (r + 1) → Fin I.n, ∀ i, I.ε v i = false → ∃ j, σ j = i := by
    refine ⟨fun j => ⟨min ((k - 1) + 2 * j.val + 1) (I.n - 1), by omega⟩, ?_⟩
    intro i hi
    rw [hε v i] at hi
    have h2 : ¬ i.val < k - 1 ∧ (i.val - (k - 1)) % 2 ≠ 0 := by
      by_cases h1 : i.val < k - 1
      · simp [h1] at hi
      · simp [h1] at hi
        exact ⟨h1, by omega⟩
    have hi' := i.isLt
    refine ⟨⟨(i.val - (k - 1)) / 2, by omega⟩, ?_⟩
    apply Fin.ext
    show min ((k - 1) + 2 * ((i.val - (k - 1)) / 2) + 1) (I.n - 1) = i.val
    omega
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨w, hw1, hw2⟩ := frame_core (I.ε v) hn σ hσ (fun a => rv I v (e a))
    (fun a => rv I v (f a)) (rv I v z) (t : ℝ) (by exact_mod_cast ht)
    (fun a b => by rw [hJ_rv, hee a b, map_zero]) (fun a b => by rw [hJ_rv, hff a b, map_zero])
    (fun a b => by rw [hJ_rv, hef a b]; split_ifs <;> simp)
    (fun a => by rw [hJ_rv, (hz a).1, map_zero]) (fun a => by rw [hJ_rv, (hz a).2, map_zero])
    (by rw [hJ_rv, hzz]; simp)
  exact ⟨w, hw1, hw2⟩

end PI.ScPiFrameW
