import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

open Formalism.MainNotions.CayleySignature

/- English proof (translation)
Introduce `i j hij`. Take `⟨i, hi⟩` from `i`. Take `⟨j, hj⟩` from `j`. Establish `hij' : i < j` using `hij`. Use `clear hij`.

Proceed by induction on `j with`. Consider the case `zero => omega`. Consider the case `succ j ih`. Establish `h1 : G < b ⟨j + 1, hj⟩ - b ⟨j, by omega⟩` using `h ⟨j, by omega⟩ hj`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hij' with hlt | heq` into its components or cases.

Establish `h2` using `ih (by omega) hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Substitute `heq` using the available equality. Conclude with `h1`.
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
Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Use `lt_sub_of_increments b G hG h i j hlt` as an intermediate fact. Conclude with `lt_abs.mpr (Or.inr (by linarith))`. Use `lt_sub_of_increments b G hG h j i hlt` as an intermediate fact. Conclude with `lt_abs.mpr (Or.inl (by linarith))`.
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
Unfold `lam48`. Conclude with `dif_neg hi`.
-/
theorem cayley_weight_high_index (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : Fin (2 * r + k + 1)) (hi : ¬ i.val < k - 1) :
    lam48 k r v b i = -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩ := by
  unfold lam48
  exact dif_neg hi

/- English proof (translation)
Establish `key : ∀ a c : Fin (2 * r + k + 1), a.val < k - 1 → ¬ c.val < k - 1 → (c.val - (k - 1)) % 2 = 1 → G ≤ |lam48 k r v b a - lam48 k r v b c|`. Introduce `a c ha hc hpar`. Establish `hk : k - 1 < 2 * r + k + 1` using `by omega`. Establish `h1` using `hanti (show a < ⟨k - 1, hk⟩ by rw [Fin.lt_def]; exact ha)`. Rewrite `h1` using `[cayley_weight_high_index k r v b ⟨k - 1, hk⟩ (by simp)]`.

Simplify using `only [Nat.sub_self] at h1`. Rewrite using `[cayley_weight_high_index k r v b c hc]`. Establish `h2` using `lt_sub_of_increments b G hG hb ⟨0, by omega⟩ ⟨c.val - (k - 1), by have := c.isLt; omega⟩ (by rw [Fin.lt_def]; simp only; omega)`. Use `le_trans ?_ (le_abs_self _)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `a c hac`. Apply the tactic sequence `by_cases ha : a.val < k - 1 <;> by_cases hc : c.val < k - 1`. It suffices to derive a contradiction. Apply `hac` to reduce the goal to its premises. Simplify using `only [eps48, if_pos ha, if_pos hc]`.

Establish `hp : (c.val - (k - 1)) % 2 = 1`. Assume the negation of the conclusion as `hne`. Apply `hac` to reduce the goal to its premises. Simplify using `only [eps48, if_pos ha, if_neg hc]`. Simplify using `[show (c.val - (k - 1)) % 2 = 0 by omega]`.

Conclude with `key a c ha hc hp`. Establish `hp : (a.val - (k - 1)) % 2 = 1`. Assume the negation of the conclusion as `hne`. Apply `hac` to reduce the goal to its premises. Simplify using `only [eps48, if_pos hc, if_neg ha]`.

Simplify using `[show (a.val - (k - 1)) % 2 = 0 by omega]`. Rewrite using `[abs_sub_comm]`. Conclude with `key c a hc ha hp`. Rewrite using `[cayley_weight_high_index k r v b a ha, cayley_weight_high_index k r v b c hc]`. Establish `hne : (⟨c.val - (k - 1), by have` using `c.isLt; omega⟩ : Fin (2 * r + 2)) ≠ ⟨a.val - (k - 1), by have := a.isLt; omega⟩ := by`.

Introduce `heq`. Apply `hac` to reduce the goal to its premises. Establish `hv : c.val - (k - 1) = a.val - (k - 1)` using `congrArg Fin.val heq`. Simplify using `only [eps48, if_neg ha, if_neg hc]`. Rewrite using `[hv]`.

Use `lt_abs_sub_of_increments b G hG hb _ _ hne` as an intermediate fact. Rewrite using `[show -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ - -b ⟨c.val - (k - 1), by have := c.isLt; omega⟩ = b ⟨c.val - (k - 1), by have := c.isLt; omega⟩ - b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ by ring]`. Conclude with `this.le`.
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
Establish `hodd : ∀ x : Fin (2 * r + k + 1), eps48 k r x = false → ¬ x.val < k - 1 ∧ (x.val - (k - 1)) % 2 = 1`. Introduce `x hx`. Unfold `eps48 at hx`. Distinguish the cases in `h1 : x.val < k - 1`. Rewrite `hx` using `[if_pos h1]`.

Conclude with `absurd hx (by decide)`. Rewrite `hx` using `[if_neg h1]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2 : ¬ ((x.val - (k - 1)) % 2 = 0)` using `by simpa using hx`. Use linear arithmetic over natural numbers and integers.

Unfold `qOf`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card_of_injOn (fun a : Fin (2 * r + k + 1) => (a.val - (k - 1)) / 2)` to reduce the goal to its premises. Introduce `a _`. Simplify using `only [Finset.mem_coe, Finset.mem_range]`.

Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `a ha c hc hac`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc`. Establish `h1` using `hodd a ha`.

Establish `h2` using `hodd c hc`. Simplify using `only at hac`. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Use `_ = r + 1 := Finset.card_range _`.
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
Substitute `hM` using the available equality. Establish `ht2 : 2 * t ≤ (2 * r + 2) * t` using `Nat.mul_le_mul (by omega) le_rfl`. Establish `hr : 10 * (r + 1) ≤ (2 * r + 2) * t`. Combine the equalities or inequalities in the displayed calculation. Use `set X := (2 * r + 2) * t with hX`.

Establish `h3 : 3 * n ≤ n + X` using `by omega`. Establish `h10 : 10 * (r + 1) ≤ n + X` using `by omega`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[Nat.zero_le (n ^ 2 * r), Nat.zero_le (n ^ 2)]`. Use `_ ≤ 2 * ((n + X) * (n + X) * (n + X)) := by gcongr`.

Use `_ = 2 * (n + X) ^ 3 := by ring`.
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
Take `⟨t, -, ht1, -, ht⟩` from `hgap`. Establish `ht1' : 2 * r + k + 1 + 5 ≤ t` using `ht1`. Take `⟨M, hM⟩ : ∃ M : ℕ, M = 2 * r + k + 1 + (2 * r + 2) * t` from `⟨_, rfl⟩`. Establish `hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), 2 * (M : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j`. Rewrite using `[hM]`.

Conclude with `ht`. Establish `hMpos : (0 : ℝ) ≤ (M : ℝ)` using `Nat.cast_nonneg _`. Establish `htpos : (0 : ℝ) ≤ (t : ℝ)` using `Nat.cast_nonneg _`. Use `⟨2 * (M : ℝ) ^ 3 + (t : ℝ) + 3, ?_, ?_⟩` and prove the remaining obligations. Conclude with `gapAtLeast_of_increments k r v b _ (by positivity) hlam.1 hb`.

Introduce `_`. Establish `hq : qOf (eps48 k r) ≤ r + 1` using `q_le_of_cayley_signature k r`. Establish `hpn : pOf (eps48 k r) ≤ 2 * r + k + 1`. Unfold `pOf; exact (Finset.card_filter_le _ _).trans (by simp)`. Establish `hqn : qOf (eps48 k r) ≤ 2 * r + k + 1`.

Unfold `qOf; exact (Finset.card_filter_le _ _).trans (by simp)`. Establish `hq0 : S7.q0 (eps48 k r) ≤ r + 1` using `(min_le_right _ _).trans hq`. Establish `hnM : 2 * r + k + 1 ≤ M` using `by rw [hM]; omega`. Establish `hnat1 : (2 * r + k + 1) * pOf (eps48 k r) * qOf (eps48 k r) ≤ M ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnat2` using `cubic_bound_of_gap_nat (2 * r + k + 1) r t M hM ht1'`. Establish `c1 : ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (eps48 k r) : ℝ) * (qOf (eps48 k r) : ℝ) ≤ (M : ℝ) ^ 3`. Conclude with `hnat1` after adjusting the coercions. Establish `c2 : (96 : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) ^ 3`. Conclude with `hnat2` after adjusting the coercions.

Establish `hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3` using `by positivity`. Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Establish `hN0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hQ0 : (0 : ℝ) ≤ (S7.q0 (eps48 k r) : ℝ)` using `Nat.cast_nonneg _`. Establish `hR1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ r + 1)`.

Establish `hRN : ((r + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : r + 1 ≤ 2 * r + k + 1)`. Establish `hQR : (S7.q0 (eps48 k r) : ℝ) ≤ ((r + 1 : ℕ) : ℝ)` using `by exact_mod_cast hq0`. Establish `hs0` using `Real.sqrt_nonneg (2 * (S7.q0 (eps48 k r) : ℝ))`. Establish `hu0` using `Real.sqrt_nonneg (2 * ((r + 1 : ℕ) : ℝ))`. Establish `hu2 : Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 = 2 * ((r + 1 : ℕ) : ℝ)` using `Real.sq_sqrt (by positivity)`.

Establish `hsu : Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))` using `Real.sqrt_le_sqrt (by linarith)`. Establish `hu1' : 1 ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))` using `by nlinarith`. Establish `hu1 : Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ≤ 2 * ((r + 1 : ℕ) : ℝ)` using `by nlinarith`. Establish `hsu' : Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) ≤ 2 * ((r + 1 : ℕ) : ℝ)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hsu hu0]`.

Establish `hQs : (S7.q0 (eps48 k r) : ℝ) * Real.sqrt (2 * (S7.q0 (eps48 k r) : ℝ)) ≤ ((r + 1 : ℕ) : ℝ) * (2 * ((r + 1 : ℕ) : ℝ))` using `mul_le_mul hQR (hsu.trans hu1) hs0 (by linarith)`. Establish `p1` using `mul_le_mul_of_nonneg_left hsu' (sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ))`. Establish `p2` using `mul_le_mul_of_nonneg_left hQs hN0`. Establish `p3` using `mul_le_mul_of_nonneg_left hRN (mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)))`. Use polynomial arithmetic with `[p1, p2, p3, c2]`.
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
