import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `h1 : A * y * η * E ≤ B * y * η * E`. Establish `: 0 ≤ y * η * E` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : B * y * η * E ≤ B * y * η * (E' + F)`. Establish `: 0 ≤ B * y * η` using `by positivity`.

Conclude with `mul_le_mul_of_nonneg_left (by linarith) this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem glue_aux {S A B y η E E' F : ℝ} (h : S ≤ A * y * η * E) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (hE : 0 ≤ E) (hEE : E ≤ E') (hF : 0 ≤ F) (hAB : A ≤ B) (hB : 0 ≤ B) :
    S ≤ B * y * η * (E' + F) := by
  have h1 : A * y * η * E ≤ B * y * η * E := by
    have : 0 ≤ y * η * E := by positivity
    nlinarith
  have h2 : B * y * η * E ≤ B * y * η * (E' + F) := by
    have : 0 ≤ B * y * η := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith

/- English proof (translation)
Introduce and unpack `⟨cA, c, A, hcA, hc, hA⟩ hB`. Take `⟨c', A', C₀, hc', hB'⟩` from `hB cA hcA`. Use `⟨min c c', max A 0 + max A' 0, C₀, lt_min hc hc', ?_⟩` and prove the remaining obligations. Introduce `M _ h8 y hy hC`. Establish `hM : 2 ≤ M`.

Establish `: 0 < M` using `Nat.pos_of_ne_zero (NeZero.ne M)`. Use `Nat.le_of_dvd this h8` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hη : 0 ≤ etaOf M` using `(etaOf_pos M hM).le`. Establish `hy0 : 0 ≤ y` using `by linarith`.

Establish `hL : 0 ≤ Real.log y` using `Real.log_nonneg (by linarith)`. Establish `hlM : 0 < Real.log M` using `Real.log_pos (by exact_mod_cast (by omega : 1 < M))`. Establish `hA0 : 0 ≤ max A 0` using `le_max_right _ _`. Establish `hA0' : 0 ≤ max A' 0` using `le_max_right _ _`. Distinguish the cases in `hr : Real.log M ≤ cA * Real.sqrt (Real.log y)`.

Establish `h` using `hA M h8 y hy hr`. Rewrite using `[add_comm (Real.exp _)]`. Use `glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)` and prove the remaining obligations. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `: min c c' * Real.sqrt (Real.log y) ≤ c * Real.sqrt (Real.log y)` using `mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `le_max_left A 0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `hB' M h8 y hy hC (not_le.mp hr)`. Use `glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)` and prove the remaining obligations.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h1 : min c c' * Real.log y ≤ c' * Real.log y` using `mul_le_mul_of_nonneg_right (min_le_right _ _) hL`. Establish `h2 : min c c' * Real.log y / Real.log M ≤ c' * Real.log y / Real.log M` using `div_le_div_of_nonneg_right h1 hlM.le`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_max_left A' 0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem glue_ranges : GlueOf := by
  rintro ⟨cA, c, A, hcA, hc, hA⟩ hB
  obtain ⟨c', A', C₀, hc', hB'⟩ := hB cA hcA
  refine ⟨min c c', max A 0 + max A' 0, C₀, lt_min hc hc', ?_⟩
  intro M _ h8 y hy hC
  have hM : 2 ≤ M := by
    have : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have := Nat.le_of_dvd this h8
    omega
  have hη : 0 ≤ etaOf M := (etaOf_pos M hM).le
  have hy0 : 0 ≤ y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hA0' : 0 ≤ max A' 0 := le_max_right _ _
  by_cases hr : Real.log M ≤ cA * Real.sqrt (Real.log y)
  · have h := hA M h8 y hy hr
    rw [add_comm (Real.exp _)]
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have : min c c' * Real.sqrt (Real.log y) ≤ c * Real.sqrt (Real.log y) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      linarith
    · have := le_max_left A 0
      linarith
  · have h := hB' M h8 y hy hC (not_le.mp hr)
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have h1 : min c c' * Real.log y ≤ c' * Real.log y :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hL
      have h2 : min c c' * Real.log y / Real.log M ≤ c' * Real.log y / Real.log M :=
        div_le_div_of_nonneg_right h1 hlM.le
      linarith
    · have := le_max_left A' 0
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
