import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICWLem

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

def ht {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) * w c

/- English proof (translation)
Establish `hcd : ((c : ℕ) : ℝ) < ((d : ℕ) : ℝ)` using `by exact_mod_cast h`. Establish `: ht (w + Pi.single c 1 - Pi.single d 1) = ht w + ((n : ℝ) - (c : ℕ)) - ((n : ℝ) - (d : ℕ))`. Simplify using `[ht, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ht_add_root {n : ℕ} (w : Fin n → ℝ) (c d : Fin n) (h : c < d) :
    ht w < ht (w + Pi.single c 1 - Pi.single d 1) := by
  have hcd : ((c : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast h
  have : ht (w + Pi.single c 1 - Pi.single d 1) =
      ht w + ((n : ℝ) - (c : ℕ)) - ((n : ℝ) - (d : ℕ)) := by
    simp [ht, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  rw [this]
  linarith

/- English proof (translation)
Introduce `n ε V _ _ E γ x hx hK`. Take `⟨g, hg, -, hwt, hdiag, -⟩` from `hG n ε`. Establish `hne : (univ.filter fun A : Finset (NC ε) => x A ≠ 0).Nonempty`. Assume the negation of the conclusion as `hc`. Apply `hx` to reduce the goal to its premises.

Use function extensionality and compare the values at `A`. Assume the negation of the conclusion as `hA`. Conclude with `hc ⟨A, by simpa using hA⟩`. Take `⟨A, hA, hmin⟩` from `Finset.exists_min_image _ (fun A : Finset (NC ε) => ht (wtA A)) hne`. Establish `hA0 : x A ≠ 0` using `by simpa using hA`.

Use `⟨A, hA0, ?_⟩` and prove the remaining obligations. Establish `hF : ∀ c d, Fop ε E c d x A = E c d (x A) + ∑ B, (g c d A B : ℂ) • x B`. Introduce `c d`. Rewrite using `[← hg V c d x A]`. Both sides reduce to the same expression.

Use `⟨fun a => ?_, fun a b hab hε => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (hK.1 a) A`. Rewrite `h1` using `[hF]`. Establish `h2 : ∑ B, (g a a A B : ℂ) • x B = (wtA A a : ℂ) • x A`. Rewrite using `[Finset.sum_eq_single A]`.

Simplify using `[hdiag]`. Introduce `B _ hB`. Simplify using `[hdiag, Ne.symm hB]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2, Pi.smul_apply]`.

Rewrite using `[Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]`. Establish `h1` using `congrFun (hK.2 a b hab hε) A`. Rewrite `h1` using `[hF]`. Establish `h2 : ∑ B, (g a b A B : ℂ) • x B = 0`. Use `Finset.sum_eq_zero fun B _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hgB : g a b A B = 0`. Simplify using `[hgB]`. Distinguish the cases in `hxB : x B = 0`. Simplify using `[hxB]`. It suffices to derive a contradiction.

Establish `h3` using `hmin B (by simpa using hxB)`. Establish `h4` using `ht_add_root (wtA B) a b hab`. Rewrite `h4` using `[← (hwt a b A B hgB).2]`. Conclude with `absurd h3 (not_le.mpr h4)`. Rewrite `h1` using `[h2, add_zero]`.

Conclude with `h1`.
-/
theorem wlem_of_gfacts (hG : GFacts) : WLem := by
  intro n ε V _ _ E γ x hx hK
  obtain ⟨g, hg, -, hwt, hdiag, -⟩ := hG n ε
  classical
  have hne : (univ.filter fun A : Finset (NC ε) => x A ≠ 0).Nonempty := by
    by_contra hc
    apply hx
    funext A
    by_contra hA
    exact hc ⟨A, by simpa using hA⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (fun A : Finset (NC ε) => ht (wtA A)) hne
  have hA0 : x A ≠ 0 := by simpa using hA
  refine ⟨A, hA0, ?_⟩
  have hF : ∀ c d, Fop ε E c d x A = E c d (x A) + ∑ B, (g c d A B : ℂ) • x B := by
    intro c d
    rw [← hg V c d x A]
    rfl
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · have h1 := congrFun (hK.1 a) A
    rw [hF] at h1
    have h2 : ∑ B, (g a a A B : ℂ) • x B = (wtA A a : ℂ) • x A := by
      rw [Finset.sum_eq_single A]
      · simp [hdiag]
      · intro B _ hB
        simp [hdiag, Ne.symm hB]
      · simp
    rw [h2, Pi.smul_apply] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]
  · have h1 := congrFun (hK.2 a b hab hε) A
    rw [hF] at h1
    have h2 : ∑ B, (g a b A B : ℂ) • x B = 0 := by
      refine Finset.sum_eq_zero fun B _ => ?_
      by_cases hgB : g a b A B = 0
      · simp [hgB]
      by_cases hxB : x B = 0
      · simp [hxB]
      exfalso
      have h3 := hmin B (by simpa using hxB)
      have h4 := ht_add_root (wtA B) a b hab
      rw [← (hwt a b A B hgB).2] at h4
      exact absurd h3 (not_le.mpr h4)
    rw [h2, add_zero] at h1
    exact h1

end GlobalTheory.CompanionTheory.DSICWLem
