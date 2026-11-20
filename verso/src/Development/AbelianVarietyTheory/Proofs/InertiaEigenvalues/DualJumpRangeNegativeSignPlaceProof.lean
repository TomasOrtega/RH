import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDual1Dot

noncomputable section

namespace GlobalTheory.Pass.JumpDualStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

/- English proof (translation)
Introduce `D hD hP i r hr eta s S sg U hs hJ Xs w hw n hsg hF`. Take `⟨hc, hj, hU⟩` from `hJ w hw`. Use `⟨insert 0 ((U w).image fun b => -b - 1), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Break down `Finset.mem_insert.1 hu with rfl | hu` into its components or cases.

Apply the tactic sequence `constructor <;> push_cast <;> omega`. Take `⟨b, hb, rfl⟩` from `Finset.mem_image.1 hu`. Take `⟨h, -, -⟩` from `hU b hb`. Establish `hs' : ((eta : ℚ) + D.R.t + 1) < s` using `by exact_mod_cast hs`. Establish `hS : (0 : ℚ) ≤ S` using `by positivity`.

Establish `ht : (1 : ℚ) ≤ D.R.t` using `by exact_mod_cast D.R.t_odd.pos`. Establish `he : (0 : ℚ) ≤ eta` using `by positivity`. Establish `key : (b : ℚ) ≤ (eta : ℚ) + D.R.t ∧ -((s : ℚ) + S) - 1 ≤ b`. Break down `h with ⟨h1, h2⟩ | h | h` into its components or cases. Establish `h1' : (0 : ℚ) ≤ b` using `by exact_mod_cast h1`.

Establish `h2' : (b : ℚ) < D.R.t` using `by exact_mod_cast h2`. Apply the tactic sequence `constructor <;> linarith`. Rewrite `h` using `[abs_le]`. Unfold `cen at h`. Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`.

Unfold `cloud cen at h`. Rewrite `h` using `[hsg]`. Simplify using `only [Bool.false_eq_true, if_false] at h`. Move the coercions through the operations in `at h`. Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`.

Establish `k1 : b ≤ (eta : ℤ) + D.R.t` using `by exact_mod_cast key.1`. Establish `k2 : -((s : ℤ) + S) - 1 ≤ b` using `by exact_mod_cast key.2`. Apply the tactic sequence `constructor <;> push_cast <;> omega`. Conclude with `(Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := U w) (f := fun b : ℤ => -b - 1); omega)`. Introduce `x τ a ha`.

Establish `h1` using `(GlobalTheory.JumpDual.jump_dual D hD hP i r hr Xs w hw n hF x τ a).1 ha`. Use `Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-a - 1, hj x τ _ h1, by ring⟩))` and prove the remaining obligations.
-/
theorem jumpDual_main : StepJumpDual := by
  intro D hD hP i r hr eta s S sg U hs hJ Xs w hw n hsg hF
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 ((U w).image fun b => -b - 1), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨h, -, -⟩ := hU b hb
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : (b : ℚ) ≤ (eta : ℚ) + D.R.t ∧ -((s : ℚ) + S) - 1 ≤ b := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ b := by exact_mod_cast h1
          have h2' : (b : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h
          simp only [Bool.false_eq_true, if_false] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : b ≤ (eta : ℤ) + D.R.t := by exact_mod_cast key.1
      have k2 : -((s : ℤ) + S) - 1 ≤ b := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := U w) (f := fun b : ℤ => -b - 1); omega)
  · intro x τ a ha
    have h1 := (GlobalTheory.JumpDual.jump_dual D hD hP i r hr Xs w hw n hF x τ a).1 ha
    refine Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-a - 1, hj x τ _ h1, by ring⟩))

end GlobalTheory.Pass.JumpDualStep
