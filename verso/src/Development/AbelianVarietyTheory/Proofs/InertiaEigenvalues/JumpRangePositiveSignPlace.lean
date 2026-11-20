import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect

noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

/- English proof (translation)
Introduce `D i r eta s S sg U hs hJ Xs w hw hsg`. Take `⟨hc, hj, hU⟩` from `hJ w hw`. Use `⟨insert 0 (U w), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Break down `Finset.mem_insert.1 hu with rfl | hu` into its components or cases.

Apply the tactic sequence `constructor <;> push_cast <;> omega`. Take `⟨h, -, -⟩` from `hU u hu`. Establish `hs' : ((eta : ℚ) + D.R.t + 1) < s` using `by exact_mod_cast hs`. Establish `hS : (0 : ℚ) ≤ S` using `by positivity`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`.

Establish `he : (0 : ℚ) ≤ eta` using `by positivity`. Establish `key : -((eta : ℚ) + D.R.t + 1) - 1 < u ∧ (u : ℚ) ≤ s + S`. Break down `h with ⟨h1, h2⟩ | h | h` into its components or cases. Establish `h1' : (0 : ℚ) ≤ u` using `by exact_mod_cast h1`. Establish `h2' : (u : ℚ) < D.R.t` using `by exact_mod_cast h2`.

Apply the tactic sequence `constructor <;> linarith`. Rewrite `h` using `[abs_le]`. Unfold `cen at h`. Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`. Unfold `cloud cen at h`.

Rewrite `h` using `[hsg]`. Simplify using `only [if_true] at h`. Move the coercions through the operations in `at h`. Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`. Establish `k1 : -((eta : ℤ) + D.R.t + 1) - 1 < u` using `by exact_mod_cast key.1`.

Establish `k2 : u ≤ (s : ℤ) + S` using `by exact_mod_cast key.2`. Apply the tactic sequence `constructor <;> push_cast <;> omega`. Conclude with `(Finset.card_insert_le _ _).trans (by omega)`. Introduce `x τ a ha`. Conclude with `Finset.mem_coe.2 (Finset.mem_insert_of_mem (hj x τ a ha))`.
-/
theorem stepJumpDirect_holds : StepJumpDirect := by
  intro D i r eta s S sg U hs hJ Xs w hw hsg
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 (U w), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨h, -, -⟩ := hU u hu
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : -((eta : ℚ) + D.R.t + 1) - 1 < u ∧ (u : ℚ) ≤ s + S := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ u := by exact_mod_cast h1
          have h2' : (u : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h; simp only [if_true] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : -((eta : ℤ) + D.R.t + 1) - 1 < u := by exact_mod_cast key.1
      have k2 : u ≤ (s : ℤ) + S := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro x τ a ha
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hj x τ a ha))

end GlobalTheory.Pass

end
