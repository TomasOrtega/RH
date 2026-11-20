import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
import Development.AutomorphicArithmetic.OrbitLabellings.FnumEqRhoMulSumOfDemandRatioLe

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ContentValue

/- English proof (translation)
Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hS : 0 ≤ ∑ a, D a` using `Finset.sum_nonneg fun a _ => hD a`. Establish `hq : (0 : ℝ) < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hg : 0 ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ a, D a` using `by positivity`. Unfold `lpF`.

Rewrite using `[sub_nonneg]`. Use `Real.sSup_le ?_ hg` and prove the remaining obligations. Introduce and unpack `t ⟨x, h0, h1, h2, rfl⟩`. Use `(GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1` as an intermediate fact. Establish `ht : 0 ≤ ∑ s, ∑ i ∈ Finset.range d, x s i` using `Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i`.

Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hq]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ l - 1 by linarith)]`. Assume the negation of the conclusion as `hc`. Use `h (h1 a i ?_)` and prove the remaining obligations. Distinguish the cases in `ho : Odd i`.

Conclude with `Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)`. Conclude with `Or.inl ho`.
-/
lemma lpF_nonneg (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ a, 0 ≤ D a) : 0 ≤ lpF l d D := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hS : 0 ≤ ∑ a, D a := Finset.sum_nonneg fun a _ => hD a
  have hq : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hg : 0 ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ a, D a := by positivity
  unfold lpF
  rw [sub_nonneg]
  refine Real.sSup_le ?_ hg
  rintro t ⟨x, h0, h1, h2, rfl⟩
  have := (GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1
  · have ht : 0 ≤ ∑ s, ∑ i ∈ Finset.range d, x s i :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ l - 1 by linarith)]
  · by_contra hc
    refine h (h1 a i ?_)
    by_cases ho : Odd i
    · exact Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)
    · exact Or.inl ho

/- English proof (translation)
Unfold `NumDatum.ordP`. Use `split`. Use `addOrderOf_pos (2 • N.hP l)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Name the introduced variables `hs`.

Establish `h0 : N.hP l ≠ 0` using `fun h => hn ⟨Or.resolve_right hc hs, h⟩`. Establish `h1 : addOrderOf (N.hP l) ≠ 1` using `fun h => h0 (AddMonoid.addOrderOf_eq_one_iff.1 h)`. Use `addOrderOf_pos (N.hP l)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma two_le_ordP (N : NumDatum) (l : ℕ) (hc : Inert N l) (hn : ¬ PhiC N l) : 2 ≤ N.ordP l := by
  unfold NumDatum.ordP
  split
  · have := addOrderOf_pos (2 • N.hP l)
    omega
  · rename_i hs
    have h0 : N.hP l ≠ 0 := fun h => hn ⟨Or.resolve_right hc hs, h⟩
    have h1 : addOrderOf (N.hP l) ≠ 1 := fun h => h0 (AddMonoid.addOrderOf_eq_one_iff.1 h)
    have := addOrderOf_pos (N.hP l)
    omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨two_le_ordP N l hc fun h => hn h.conjIn, even_ordP_of_not_conjIn hc hn⟩`.
-/
lemma two_le_ordP_and_even (N : NumDatum) (l : ℕ) (hc : Inert N l) (hn : ¬ ConjIn N l) : 2 ≤ N.ordP l ∧ Even (N.ordP l) :=
  ⟨two_le_ordP N l hc fun h => hn h.conjIn, even_ordP_of_not_conjIn hc hn⟩

/- English proof (translation)
Establish `h4 : 4 ≤ l ^ 2` using `by nlinarith`. Rewrite using `[← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]`. Establish `h1 : 0 ≤ k * w` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg h1 (show 0 ≤ l ^ 2 - 2 by linarith), mul_nonneg hw (show 0 ≤ l ^ 2 by linarith)]`.
-/
lemma rho_bound (k w l : ℝ) (hk : 1 ≤ k) (hw : 0 ≤ w) (hl : 2 ≤ l) :
    (k - 1) * w / (l ^ 2 - 1) ≤ 2 * (k * w / l ^ 2) := by
  have h4 : 4 ≤ l ^ 2 := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ k * w := by positivity
  nlinarith [mul_nonneg h1 (show 0 ≤ l ^ 2 - 2 by linarith), mul_nonneg hw (show 0 ≤ l ^ 2 by linarith)]

/- English proof (translation)
Introduce `N j l hp h2 hq hd hg0 hg1 hw hr`. Establish `hl : 2 ≤ l` using `hp.two_le`. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hk : (1 : ℝ) ≤ N.R.k`. Use `N.R.m_add_three_le_k` as an intermediate fact.

Conclude with `(by omega : 1 ≤ N.R.k)` after adjusting the coercions. Establish `hq2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hS : 0 ≤ ∑ z, N.w j z` using `Finset.sum_nonneg fun z _ => hw z`. Establish `hcls : Inert N l ∨ N.cls l = PrimeClass.splitK`. Unfold `Inert NumDatum.cls primeClass`.

Rewrite using `[if_neg h2, if_neg hq, if_neg hd]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hnd : N.cls l ≠ PrimeClass.ramD`. Apply the tactic sequence `rcases hcls with (h | h) | h <;> rw [h] <;> simp`. Establish `hF : N.FjP j l = if Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n then N.FInert j l else 0`.

Unfold `NumDatum.FjP`. Rewrite using `[if_neg (by tauto), if_neg hnd]`. Distinguish the cases in `h : Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n`. Rewrite using `[if_pos h]`. Conclude with `if_pos h`.

Rewrite using `[if_neg h]`. Conclude with `if_neg h`. Establish `hD : ∀ z, 0 ≤ ((N.R.k : ℝ) - 1) * N.w j z` using `fun z => mul_nonneg (by linarith) (hw z)`. Establish `hI : 0 ≤ N.FInert j l`. Unfold `NumDatum.FInert`.

Use `split_ifs`. Conclude with `Finset.sum_nonneg fun z _ => div_nonneg (hD z) hq2.le`. Conclude with `div_nonneg (Finset.sum_nonneg fun z _ => lpF_nonneg _ _ _ hl fun a => hD _) (Nat.cast_nonneg _)`. Establish `hb` using `rho_bound N.R.k _ l hk hS hl'`. Use `⟨?_, hcls, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hF] split_ifs`. Conclude with `hI`. Conclude with `le_rfl`. Establish `h3` using `N.R.m_add_three_le_k`. Establish `h4` using `N.R.two_le_m`.

Use `⟨?_, ?_, h3, ?_, ?_⟩` and prove the remaining obligations. Use `show Fintype.card (RPl N.R) = N.R.f`. Use `Formalism.HC.Frame.card_A N.R.toFrame` as an intermediate fact. Simplify `this` using `[Ranks.f, Ranks.n]`. Use `show 1 ≤ N.R.m`.

Use linear arithmetic over natural numbers and integers. Use `show N.R.r = N.R.k - 1 + N.R.m`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Use `show 0 ≤ N.Sc + N.eta`.

Unfold `NumDatum.Sc NumDatum.eta`. Check the signs of the components of the expression. Introduce `hc`. Establish `hi : Inert N l` using `Or.inl hc.1`. Distinguish the cases in `hX : (l : ℝ) ≤ N.sc.X'' N.R.n`.

Rewrite using `[hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]`. Unfold `NumDatum.FInert`. Rewrite using `[if_pos (show N.cls l = PrimeClass.inertClass ∧ N.hP l = 0 from hc), ← Finset.sum_div, ← Finset.mul_sum]`. Rewrite using `[hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]`. Conclude with `hb`.

Introduce `hi hc Z hZ`. Establish `hZ' : Formalism.L2.FormalSeriesBounds.IsReps N l Z` using `hZ`. Distinguish the cases in `hX : (l : ℝ) ≤ N.sc.X'' N.R.n`. Rewrite using `[hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]`. Conclude with `(GlobalTheory.LevelsOrbits.fInertReps N j l Z hZ' hi hc).1.ge`.

Rewrite using `[hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]`. Use `le_trans (le_of_eq ?_) hb` and prove the remaining obligations. Establish `ho2` using `two_le_ordP N l hi hc`. Establish `hl3 : 3 ≤ l`. Use `ne_two_of_not_small h2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hbal : ∀ z z', N.w j z' ≤ l * N.w j z` using `fun z z' => (hr z z').trans (mul_le_mul_of_nonneg_right (not_le.1 hX).le (hw z))`. Rewrite using `[GlobalTheory.LevelsOrbits.sum_reps N l Z hZ' (N.w j), Finset.mul_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le l (N.ordP l) hl3 ho2 _ (fun a => hD _) (fun a a' => ?_), ← Finset.mul_sum]`.

Unfold `Formalism.IncomingBounds.rho`. Expand and normalize the polynomial expressions, which then agree. Use `mul_le_mul_of_nonneg_left (hbal (N.pos l z a.val) (N.pos l z a'.val)) (show (0 : ℝ) ≤ N.R.k - 1 by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (N : NumDatum) (j l : ℕ), l.Prime → l ∉ N.H.small → l ≠ N.q → l ≠ N.d → l ≠ N.g 0 → l ≠ N.g 1 → (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z) →
  0 ≤ N.FjP j l ∧ (Inert N l ∨ N.cls l = PrimeClass.splitK) ∧ ParOK (parOf N j l) ∧
  (PhiC N l → ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ∧
  (Inert N l → ¬ PhiC N l → ∀ Z : Finset (RPl N.R), RF.IsReps (parOf N j l) Z →
    (∑ z ∈ Z, Fnum l (N.ordP l) fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) := by
  classical
  intro N j l hp h2 hq hd hg0 hg1 hw hr
  have hl : 2 ≤ l := hp.two_le
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk : (1 : ℝ) ≤ N.R.k := by
    have := N.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ N.R.k)
  have hq2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hS : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hw z
  have hcls : Inert N l ∨ N.cls l = PrimeClass.splitK := by
    unfold Inert NumDatum.cls primeClass
    rw [if_neg h2, if_neg hq, if_neg hd]
    split_ifs <;> simp
  have hnd : N.cls l ≠ PrimeClass.ramD := by
    rcases hcls with (h | h) | h <;> rw [h] <;> simp
  have hF : N.FjP j l = if Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n then N.FInert j l else 0 := by
    unfold NumDatum.FjP
    rw [if_neg (by tauto), if_neg hnd]
    by_cases h : Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [if_pos h]; exact if_pos h
    · rw [if_neg h]; exact if_neg h
  have hD : ∀ z, 0 ≤ ((N.R.k : ℝ) - 1) * N.w j z := fun z => mul_nonneg (by linarith) (hw z)
  have hI : 0 ≤ N.FInert j l := by
    unfold NumDatum.FInert
    split_ifs
    · exact Finset.sum_nonneg fun z _ => div_nonneg (hD z) hq2.le
    · exact div_nonneg (Finset.sum_nonneg fun z _ => lpF_nonneg _ _ _ hl fun a => hD _) (Nat.cast_nonneg _)
  have hb := rho_bound N.R.k _ l hk hS hl'
  refine ⟨?_, hcls, ?_, ?_, ?_⟩
  · rw [hF]
    split_ifs
    · exact hI
    · exact le_rfl
  · have h3 := N.R.m_add_three_le_k
    have h4 := N.R.two_le_m
    refine ⟨?_, ?_, h3, ?_, ?_⟩
    · show Fintype.card (RPl N.R) = N.R.f
      have := Formalism.HC.Frame.card_A N.R.toFrame
      simpa [Ranks.f, Ranks.n] using this
    · show 1 ≤ N.R.m
      omega
    · show N.R.r = N.R.k - 1 + N.R.m
      unfold Ranks.r
      omega
    · show 0 ≤ N.Sc + N.eta
      unfold NumDatum.Sc NumDatum.eta
      positivity
  · intro hc
    have hi : Inert N l := Or.inl hc.1
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      unfold NumDatum.FInert
      rw [if_pos (show N.cls l = PrimeClass.inertClass ∧ N.hP l = 0 from hc), ← Finset.sum_div, ← Finset.mul_sum]
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      exact hb
  · intro hi hc Z hZ
    have hZ' : Formalism.L2.FormalSeriesBounds.IsReps N l Z := hZ
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      exact (GlobalTheory.LevelsOrbits.fInertReps N j l Z hZ' hi hc).1.ge
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      refine le_trans (le_of_eq ?_) hb
      have ho2 := two_le_ordP N l hi hc
      have hl3 : 3 ≤ l := by
        have := ne_two_of_not_small h2
        omega
      have hbal : ∀ z z', N.w j z' ≤ l * N.w j z := fun z z' =>
        (hr z z').trans (mul_le_mul_of_nonneg_right (not_le.1 hX).le (hw z))
      rw [GlobalTheory.LevelsOrbits.sum_reps N l Z hZ' (N.w j), Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le l (N.ordP l) hl3 ho2 _ (fun a => hD _) (fun a a' => ?_), ← Finset.mul_sum]
      · unfold Formalism.IncomingBounds.rho
        ring
      · have := mul_le_mul_of_nonneg_left (hbal (N.pos l z a.val) (N.pos l z a'.val))
          (show (0 : ℝ) ≤ N.R.k - 1 by linarith)
        linarith

end GlobalTheory.ContentValue
