import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace GrowthPolynomialOperator

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [actM, Xp, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.single_apply, ite_smul, zero_smul, ite_and]`. Simplify using `[Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
lemma actM_Xp {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Xp a b) = ((1 + Complex.I) / 2) • E a b + ((1 - Complex.I) / 2) • E b a := by
  simp only [actM, Xp, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.single_apply, ite_smul, zero_smul, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Apply the tactic sequence `apply Finset.sum_nbij' Prod.swap Prod.swap <;> simp [nc, ne_comm]`.
-/
lemma sum_nc_swap {β : Type*} [AddCommMonoid β] (ε : Fin n → Bool) (g : Fin n × Fin n → β) :
    ∑ p ∈ nc ε, g p.swap = ∑ p ∈ nc ε, g p := by
  apply Finset.sum_nbij' Prod.swap Prod.swap <;> simp [nc, ne_comm]

/- English proof (translation)
Simplify using `only [Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_id (x y : ℂ) :
    ‖(1 + Complex.I) / 2 * x + (1 - Complex.I) / 2 * y‖ ^ 2 +
      ‖(1 + Complex.I) / 2 * y + (1 - Complex.I) / 2 * x‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  ring

/- English proof (translation)
Put the polynomial expressions in normal form. Simplify using `[Complex.I_sq]`.
-/
lemma coef1 : ((1 + Complex.I) / 2) ^ 2 + ((1 - Complex.I) / 2) ^ 2 = 0 := by
  ring_nf; simp [Complex.I_sq]

/- English proof (translation)
Take the linear combination `(-1/2 : ℂ) * Complex.I_sq`.
-/
lemma coef2 : (1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1 := by
  linear_combination (-1/2 : ℂ) * Complex.I_sq

/- English proof (translation)
Establish `hab : a ≠ b` using `fun e => h (e ▸ rfl)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `inG`. Use extensionality with `i j`. Simplify using `[Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply, ← sub_eq_add_neg]`.

Distinguish the cases in `h1 : a = i ∧ b = j`. Take `⟨h1a, h1b⟩` from `h1`. Substitute `h1a` using the available equality. Substitute `h1b` using the available equality. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring`.

Distinguish the cases in `h2 : b = i ∧ a = j`. Take `⟨h2a, h2b⟩` from `h2`. Substitute `h2a` using the available equality. Substitute `h2b` using the available equality. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring`.

Simplify using `[h1, h2]`. Use extensionality with `i j`. Simplify using `[Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]`. Distinguish the cases in `h1 : a = i ∧ b = j`. Take `⟨h1a, h1b⟩` from `h1`.

Substitute `h1a` using the available equality. Substitute `h1b` using the available equality. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring`. Distinguish the cases in `h2 : b = i ∧ a = j`. Take `⟨h2a, h2b⟩` from `h2`.

Substitute `h2a` using the available equality. Substitute `h2b` using the available equality. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring`. Simplify using `[h1, h2]`.
-/
lemma inP_Xp (ε : Fin n → Bool) (a b : Fin n) (h : ε a ≠ ε b) : inP ε (Xp a b) := by
  have hab : a ≠ b := fun e => h (e ▸ rfl)
  refine ⟨?_, ?_⟩
  · unfold inG
    ext i j
    simp [Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply, ← sub_eq_add_neg]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      subst h1b
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
    · by_cases h2 : b = i ∧ a = j
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        subst h2b
        cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
      · simp [h1, h2]
  · ext i j
    simp [Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      subst h1b
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
    · by_cases h2 : b = i ∧ a = j
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        subst h2b
        cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
      · simp [h1, h2]

end GrowthPolynomialOperator

open GrowthPolynomialOperator in
/- English proof (translation)
Introduce `hA n ε V _ _ E hm`. Take `⟨_, _, _, h4⟩` from `hA n ε V E hm`. Use `⟨fun p hp => inP_Xp ε p.1 p.2 (by simpa [nc] using hp), fun κ hκ v => ?_, fun f w => ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ a b : Fin n, actM E (Xp a b) (actM E (Xp a b) v) = ((1 + Complex.I) / 2) ^ 2 • E a b (E a b v) + ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2)) • E a b (E b a v) + ((1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) • E b a (E a b v) + ((1 - Complex.I) / 2) ^ 2 • E b a (E b a …`. Introduce `a b`.

Rewrite using `[actM_Xp]`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]`. Use `module`. Rewrite using `[Finset.sum_congr rfl (fun p _ => hterm p.1 p.2)]`. Simplify using `only [Finset.sum_add_distrib, ← Finset.smul_sum]`.

Establish `s1` using `sum_nc_swap ε (fun p => E p.1 p.2 (E p.1 p.2 v))`. Establish `s2` using `sum_nc_swap ε (fun p => E p.1 p.2 (E p.2 p.1 v))`. Simplify using `only [Prod.fst_swap, Prod.snd_swap] at s1 s2`. Rewrite using `[s1, s2, ← (h4 κ hκ v).2.2]`. Combine the equalities or inequalities in the displayed calculation.

Establish `key : ∀ p ∈ nc ε, ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2 + ‖f (actM E (Xp p.2 p.1) w)‖ ^ 2 = ‖f (E p.1 p.2 w)‖ ^ 2 + ‖f (E p.2 p.1 w)‖ ^ 2`. Introduce `p _`. Simplify using `only [actM_Xp, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul]`. Conclude with `norm_id _ _`. Establish `h1` using `sum_nc_swap ε (fun p => ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2)`.

Establish `h2` using `sum_nc_swap ε (fun p => ‖f (E p.1 p.2 w)‖ ^ 2)`. Simplify using `only [Prod.fst_swap, Prod.snd_swap] at h1 h2`. Establish `h3` using `Finset.sum_congr rfl key`. Rewrite `h3` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem growth_of_basic : A0 → B1 := by
  intro hA n ε V _ _ E hm
  obtain ⟨_, _, _, h4⟩ := hA n ε V E hm
  refine ⟨fun p hp => inP_Xp ε p.1 p.2 (by simpa [nc] using hp), fun κ hκ v => ?_, fun f w => ?_⟩
  · have hterm : ∀ a b : Fin n, actM E (Xp a b) (actM E (Xp a b) v) =
        ((1 + Complex.I) / 2) ^ 2 • E a b (E a b v) + ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2)) • E a b (E b a v) +
        ((1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) • E b a (E a b v) + ((1 - Complex.I) / 2) ^ 2 • E b a (E b a v) := by
      intro a b
      rw [actM_Xp]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
      module
    rw [Finset.sum_congr rfl (fun p _ => hterm p.1 p.2)]
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    have s1 := sum_nc_swap ε (fun p => E p.1 p.2 (E p.1 p.2 v))
    have s2 := sum_nc_swap ε (fun p => E p.1 p.2 (E p.2 p.1 v))
    simp only [Prod.fst_swap, Prod.snd_swap] at s1 s2
    rw [s1, s2, ← (h4 κ hκ v).2.2]
    calc _ = (((1 + Complex.I) / 2) ^ 2 + ((1 - Complex.I) / 2) ^ 2) • ∑ p ∈ nc ε, E p.1 p.2 (E p.1 p.2 v) +
          ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) •
            ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 v) := by module
      _ = _ := by rw [coef1, coef2]; simp
  · have key : ∀ p ∈ nc ε, ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2 + ‖f (actM E (Xp p.2 p.1) w)‖ ^ 2 =
        ‖f (E p.1 p.2 w)‖ ^ 2 + ‖f (E p.2 p.1 w)‖ ^ 2 := by
      intro p _
      simp only [actM_Xp, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul]
      exact norm_id _ _
    have h1 := sum_nc_swap ε (fun p => ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2)
    have h2 := sum_nc_swap ε (fun p => ‖f (E p.1 p.2 w)‖ ^ 2)
    simp only [Prod.fst_swap, Prod.snd_swap] at h1 h2
    have h3 := Finset.sum_congr rfl key
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2] at h3
    linarith

end PositivityTheory.CW

end
