import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

open Formalism.MainNotions.CayleySignature

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem lt_sub_of_increments {m : ℕ} (b : Fin m → ℝ) (G : ℝ) (hG : 0 < G)
    (h : ∀ (j : Fin m) (hj : j.val + 1 < m), G < b ⟨j.val + 1, hj⟩ - b j) :
    ∀ i j : Fin m, i < j → G < b j - b i := by
  intro i j hij
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij' : i < j := hij
  clear hij
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 : G < b ⟨j + 1, hj⟩ - b ⟨j, by omega⟩ := h ⟨j, by omega⟩ hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij' with hlt | heq
    · have h2 := ih (by omega) hlt
      linarith
    · subst heq
      exact h1

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem lt_abs_sub_of_increments {m : ℕ} (b : Fin m → ℝ) (G : ℝ) (hG : 0 < G)
    (h : ∀ (j : Fin m) (hj : j.val + 1 < m), G < b ⟨j.val + 1, hj⟩ - b j)
    (i j : Fin m) (hij : i ≠ j) : G < |b i - b j| := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have := lt_sub_of_increments b G hG h i j hlt
    exact lt_abs.mpr (Or.inr (by linarith))
  · have := lt_sub_of_increments b G hG h j i hlt
    exact lt_abs.mpr (Or.inl (by linarith))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem cayley_weight_high_index (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : Fin (2 * r + k + 1)) (hi : ¬ i.val < k - 1) :
    lam48 k r v b i = -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩ := by
  unfold lam48
  exact dif_neg hi

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Combine the linear equalities and inequalities to obtain the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem gapAtLeast_of_increments (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (G : ℝ) (hG : 0 < G)
    (hanti : StrictAnti (lam48 k r v b))
    (hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), G < b ⟨j.val + 1, hj⟩ - b j) :
    GapAtLeast (eps48 k r) (lam48 k r v b) G := by
  have key : ∀ a c : Fin (2 * r + k + 1), a.val < k - 1 → ¬ c.val < k - 1 → (c.val - (k - 1)) % 2 = 1 →
      G ≤ |lam48 k r v b a - lam48 k r v b c| := by
    intro a c ha hc hpar
    have hk : k - 1 < 2 * r + k + 1 := by omega
    have h1 := hanti (show a < ⟨k - 1, hk⟩ by rw [Fin.lt_def]; exact ha)
    rw [cayley_weight_high_index k r v b ⟨k - 1, hk⟩ (by simp)] at h1
    simp only [Nat.sub_self] at h1
    rw [cayley_weight_high_index k r v b c hc]
    have h2 := lt_sub_of_increments b G hG hb ⟨0, by omega⟩ ⟨c.val - (k - 1), by have := c.isLt; omega⟩
      (by rw [Fin.lt_def]; simp only; omega)
    refine le_trans ?_ (le_abs_self _)
    linarith
  intro a c hac
  by_cases ha : a.val < k - 1 <;> by_cases hc : c.val < k - 1
  · exfalso; apply hac; simp only [eps48, if_pos ha, if_pos hc]
  · have hp : (c.val - (k - 1)) % 2 = 1 := by
      by_contra hne
      apply hac
      simp only [eps48, if_pos ha, if_neg hc]
      simp [show (c.val - (k - 1)) % 2 = 0 by omega]
    exact key a c ha hc hp
  · have hp : (a.val - (k - 1)) % 2 = 1 := by
      by_contra hne
      apply hac
      simp only [eps48, if_pos hc, if_neg ha]
      simp [show (a.val - (k - 1)) % 2 = 0 by omega]
    rw [abs_sub_comm]; exact key c a hc ha hp
  · rw [cayley_weight_high_index k r v b a ha, cayley_weight_high_index k r v b c hc]
    have hne : (⟨c.val - (k - 1), by have := c.isLt; omega⟩ : Fin (2 * r + 2)) ≠
        ⟨a.val - (k - 1), by have := a.isLt; omega⟩ := by
      intro heq
      apply hac
      have hv : c.val - (k - 1) = a.val - (k - 1) := congrArg Fin.val heq
      simp only [eps48, if_neg ha, if_neg hc]
      rw [hv]
    have := lt_abs_sub_of_increments b G hG hb _ _ hne
    rw [show -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ - -b ⟨c.val - (k - 1), by have := c.isLt; omega⟩ =
      b ⟨c.val - (k - 1), by have := c.isLt; omega⟩ - b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ by ring]
    exact this.le

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Replace the relevant objects with their definitions.

Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify by unfolding definitions. Reduce the claim to the hypotheses of an applicable result. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem q_le_of_cayley_signature (k r : ℕ) : qOf (eps48 k r) ≤ r + 1 := by
  have hodd : ∀ x : Fin (2 * r + k + 1), eps48 k r x = false →
      ¬ x.val < k - 1 ∧ (x.val - (k - 1)) % 2 = 1 := by
    intro x hx
    unfold eps48 at hx
    by_cases h1 : x.val < k - 1
    · rw [if_pos h1] at hx
      exact absurd hx (by decide)
    · rw [if_neg h1] at hx
      refine ⟨h1, ?_⟩
      have h2 : ¬ ((x.val - (k - 1)) % 2 = 0) := by simpa using hx
      omega
  unfold qOf
  calc (Finset.univ.filter fun a => eps48 k r a = false).card
      ≤ (Finset.range (r + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin (2 * r + k + 1) => (a.val - (k - 1)) / 2)
        · intro a _
          simp only [Finset.mem_coe, Finset.mem_range]
          have := a.isLt
          omega
        · intro a ha c hc hac
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
          have h1 := hodd a ha
          have h2 := hodd c hc
          dsimp only at hac
          apply Fin.ext
          omega
    _ = r + 1 := Finset.card_range _

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem cubic_bound_of_gap_nat (n r t M : ℕ) (hM : M = n + (2 * r + 2) * t) (ht : n + 5 ≤ t) :
    96 * n ^ 2 * (r + 1) ≤ 2 * M ^ 3 := by
  subst hM
  have ht2 : 2 * t ≤ (2 * r + 2) * t := Nat.mul_le_mul (by omega) le_rfl
  have hr : 10 * (r + 1) ≤ (2 * r + 2) * t := by
    calc 10 * (r + 1) ≤ (2 * r + 2) * 5 := by omega
      _ ≤ (2 * r + 2) * t := Nat.mul_le_mul le_rfl (by omega)
  set X := (2 * r + 2) * t with hX
  have h3 : 3 * n ≤ n + X := by omega
  have h10 : 10 * (r + 1) ≤ n + X := by omega
  calc 96 * n ^ 2 * (r + 1) ≤ 2 * ((3 * n) * (3 * n) * (10 * (r + 1))) := by
        nlinarith [Nat.zero_le (n ^ 2 * r), Nat.zero_le (n ^ 2)]
    _ ≤ 2 * ((n + X) * (n + X) * (n + X)) := by gcongr
    _ = 2 * (n + X) ^ 3 := by ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem cayley_weight_gap (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hlam : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hgap : Formalism.MainNotions.CayleySignature.GapBig k r b) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h ∧
      (1 ≤ S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r) →
        ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ) * (qOf (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ) + 1 < h ∧
        8 * Real.sqrt (2 * (S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ)) *
            (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) +
              2 * ((2 * r + k + 1 : ℕ) : ℝ) * S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r)) < h) := by
  obtain ⟨t, -, ht1, -, ht⟩ := hgap
  have ht1' : 2 * r + k + 1 + 5 ≤ t := ht1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * r + k + 1 + (2 * r + 2) * t := ⟨_, rfl⟩
  have hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * (M : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j := by
    rw [hM]; exact ht
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have htpos : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  refine ⟨2 * (M : ℝ) ^ 3 + (t : ℝ) + 3, ?_, ?_⟩
  · exact gapAtLeast_of_increments k r v b _ (by positivity) hlam.1 hb
  · intro _
    have hq : qOf (eps48 k r) ≤ r + 1 := q_le_of_cayley_signature k r
    have hpn : pOf (eps48 k r) ≤ 2 * r + k + 1 := by
      unfold pOf; exact (Finset.card_filter_le _ _).trans (by simp)
    have hqn : qOf (eps48 k r) ≤ 2 * r + k + 1 := by
      unfold qOf; exact (Finset.card_filter_le _ _).trans (by simp)
    have hq0 : S7.q0 (eps48 k r) ≤ r + 1 := (min_le_right _ _).trans hq
    have hnM : 2 * r + k + 1 ≤ M := by rw [hM]; omega
    have hnat1 : (2 * r + k + 1) * pOf (eps48 k r) * qOf (eps48 k r) ≤ M ^ 3 := by
      calc _ ≤ M * M * M := Nat.mul_le_mul (Nat.mul_le_mul hnM (hpn.trans hnM)) (hqn.trans hnM)
        _ = M ^ 3 := by ring
    have hnat2 := cubic_bound_of_gap_nat (2 * r + k + 1) r t M hM ht1'
    have c1 : ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (eps48 k r) : ℝ) * (qOf (eps48 k r) : ℝ) ≤ (M : ℝ) ^ 3 := by
      exact_mod_cast hnat1
    have c2 : (96 : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) ^ 3 := by
      exact_mod_cast hnat2
    have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
    refine ⟨by linarith, ?_⟩
    have hN0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ (S7.q0 (eps48 k r) : ℝ) := Nat.cast_nonneg _
    have hR1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
    have hRN : ((r + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ 2 * r + k + 1)
    have hQR : (S7.q0 (eps48 k r) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast hq0
    have hs0 := Real.sqrt_nonneg (2 * (S7.q0 (eps48 k r) : ℝ))
    have hu0 := Real.sqrt_nonneg (2 * ((r + 1 : ℕ) : ℝ))
    have hu2 : Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 = 2 * ((r + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    have hsu : Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hu1' : 1 ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) := by nlinarith
    have hu1 : Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ≤ 2 * ((r + 1 : ℕ) : ℝ) := by nlinarith
    have hsu' : Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ≤
        2 * ((r + 1 : ℕ) : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hsu hu0]
    have hQs : (S7.q0 (eps48 k r) : ℝ) * Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) ≤
        ((r + 1 : ℕ) : ℝ) * (2 * ((r + 1 : ℕ) : ℝ)) :=
      mul_le_mul hQR (hsu.trans hu1) hs0 (by linarith)
    have p1 := mul_le_mul_of_nonneg_left hsu' (sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ))
    have p2 := mul_le_mul_of_nonneg_left hQs hN0
    have p3 := mul_le_mul_of_nonneg_left hRN (mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)))
    nlinarith [p1, p2, p3, c2]

end ReciprocityTheory.ChartRestriction.DS
