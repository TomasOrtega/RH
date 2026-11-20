import Mathlib

/- English proof (translation)
Introduce `C Ω J _ _ _ f`. Establish `hsum : ∑ j : J, f (Pi.single j 1) = 1`. Rewrite using `[← map_sum]`. Establish `h : (∑ j : J, (Pi.single j (1 : C) : J → C)) = 1`. Simplify using `using Finset.univ_sum_single (1 : J → C)`.

Rewrite using `[h, map_one]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j : J, f (Pi.single j 1) ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Rewrite `hsum` using `[Finset.sum_eq_zero (fun j _ => hne j)]`.

Conclude with `zero_ne_one hsum`. Establish `hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1)`. Rewrite using `[← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hi]`. Establish `hone : f (Pi.single j 1) = 1`.

Conclude with `mul_left_cancel₀ hj (by rw [hidem, mul_one])`. Use `⟨j, fun v => ?_⟩` and prove the remaining obligations. Establish `hmul : v * Pi.single j 1 = (Algebra.algebraMap C (J → C) : C → J → C) (v j) * Pi.single j 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`.

Substitute `hi` using the available equality. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Simplify using `[Pi.single_eq_of_ne hi]`. Establish `h2` using `congrArg f hmul`. Simplify `h2` using `[map_mul, hone]`.
-/
theorem UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval :
    ∀ {C Ω J : Type}
    [inst : CommRing C] [inst_1 : Field Ω] [Fintype J] (f : (J → C) →+* Ω),
    ∃ (j : J),
      ∀ (v : J → C), (f : (J → C) → Ω) v = (f : (J → C) → Ω) ((Algebra.algebraMap C (J → C) : C → J → C) (v j)) := by
  intro C Ω J _ _ _ f
  classical
  have hsum : ∑ j : J, f (Pi.single j 1) = 1 := by
    rw [← map_sum]
    have h : (∑ j : J, (Pi.single j (1 : C) : J → C)) = 1 := by
      simpa using Finset.univ_sum_single (1 : J → C)
    rw [h, map_one]
  obtain ⟨j, hj⟩ : ∃ j : J, f (Pi.single j 1) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun j _ => hne j)] at hsum
    exact zero_ne_one hsum
  have hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
    rw [← map_mul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  have hone : f (Pi.single j 1) = 1 := by
    exact mul_left_cancel₀ hj (by rw [hidem, mul_one])
  refine ⟨j, fun v => ?_⟩
  have hmul : v * Pi.single j 1 =
      (Algebra.algebraMap C (J → C) : C → J → C) (v j) * Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hi]
  have h2 := congrArg f hmul
  simpa [map_mul, hone] using h2
