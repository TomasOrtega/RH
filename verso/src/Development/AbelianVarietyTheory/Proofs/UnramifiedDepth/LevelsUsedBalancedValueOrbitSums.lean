import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Formalism.LocalRingCardinality.DataForced
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CyclicSolvable

open Formalism.L2.FormalSeriesBounds Formalism.L2.DIV Formalism.BasicNotions Formalism.UnitaryBoundIntegral

namespace GlobalTheory.LevelsOrbits

/- English proof (translation)
Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt ((k : ℝ) ^ ((3 : ℝ) / 2)) (show (1 : ℝ) < l by linarith)`. Use `⟨2 * n + 3, ⟨n + 1, by ring⟩, by omega, hn.trans_le ?_⟩` and prove the remaining obligations. Conclude with `pow_le_pow_right₀ (by linarith) (by omega)`.
-/
lemma levels_nonempty (k l : ℕ) (hl : 2 ≤ l) :
    {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}.Nonempty := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((k : ℝ) ^ ((3 : ℝ) / 2)) (show (1 : ℝ) < l by linarith)
  refine ⟨2 * n + 3, ⟨n + 1, by ring⟩, by omega, hn.trans_le ?_⟩
  exact pow_le_pow_right₀ (by linarith) (by omega)

/- English proof (translation)
Introduce `k l _ hl`. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hm` using `Nat.sInf_mem (levels_nonempty k l hl)`. Use `⟨hm.1, hm.2.1, hm.2.2, ?_⟩` and prove the remaining obligations. Unfold `thl`.

Use `IsGreatest.csSup_eq ⟨⟨_, hm.1, hm.2.1, hm.2.2, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨i, h1, h2, h3, rfl⟩`. Establish `hi : i0 k l ≤ i` using `Nat.sInf_le ⟨h1, h2, h3⟩`. Conclude with `inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) hi)`.
-/
theorem thlEq : ThlEq := by
  intro k l _ hl
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hm := Nat.sInf_mem (levels_nonempty k l hl)
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  unfold thl
  refine IsGreatest.csSup_eq ⟨⟨_, hm.1, hm.2.1, hm.2.2, rfl⟩, ?_⟩
  rintro t ⟨i, h1, h2, h3, rfl⟩
  have hi : i0 k l ≤ i := Nat.sInf_le ⟨h1, h2, h3⟩
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) hi)

/- English proof (translation)
Introduce `k l hk hl`. Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hlog : 0 ≤ Real.log k` using `Real.log_nonneg hk'`. Take `⟨⟨r, hr⟩, h3, -, -⟩` from `thlEq k l hk (by omega)`.

Distinguish the cases in `h : i0 k l = 3`. Rewrite using `[h]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j, hj⟩ : ∃ j, i0 k l = j + 2` from `⟨i0 k l - 2, by omega⟩`.

Establish `hn : j ∉ {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}` using `Nat.notMem_of_lt_sInf (show j < i0 k l by omega)`. Establish `hle : (l : ℝ) ^ j ≤ (k : ℝ) ^ ((3 : ℝ) / 2)`. Assume the negation of the conclusion as `hc`. Conclude with `hn ⟨⟨r - 1, by omega⟩, by omega, not_le.1 hc⟩`. Establish `h1` using `Real.log_le_log (by positivity) hle`.

Rewrite `h1` using `[Real.log_pow, Real.log_rpow (by linarith)]`. Establish `h2 : 1 ≤ Real.log l`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : (j : ℝ) ≤ j * Real.log l` using `le_mul_of_one_le_right (by positivity) h2`. Rewrite using `[hj]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levelBound : LevelBound := by
  intro k l hk hl
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk'
  obtain ⟨⟨r, hr⟩, h3, -, -⟩ := thlEq k l hk (by omega)
  by_cases h : i0 k l = 3
  · rw [h]; push_cast; linarith
  · obtain ⟨j, hj⟩ : ∃ j, i0 k l = j + 2 := ⟨i0 k l - 2, by omega⟩
    have hn : j ∉ {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i} :=
      Nat.notMem_of_lt_sInf (show j < i0 k l by omega)
    have hle : (l : ℝ) ^ j ≤ (k : ℝ) ^ ((3 : ℝ) / 2) := by
      by_contra hc
      exact hn ⟨⟨r - 1, by omega⟩, by omega, not_le.1 hc⟩
    have h1 := Real.log_le_log (by positivity) hle
    rw [Real.log_pow, Real.log_rpow (by linarith)] at h1
    have h2 : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have h4 : (j : ℝ) ≤ j * Real.log l := le_mul_of_one_le_right (by positivity) h2
    rw [hj]; push_cast; linarith

/- English proof (translation)
Unfold `Formalism.IncomingBounds.oddLevels`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `[Finset.mem_range.1 hi]`.
-/
lemma sum_range_ite (d : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then f i else 0) = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, f i := by
  unfold Formalism.IncomingBounds.oddLevels
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Finset.mem_range.1 hi]

/- English proof (translation)
Unfold `Formalism.IncomingBounds.oddLevels`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `hf i h`.
-/
lemma sum_range_eq (d : ℕ) (f : ℕ → ℝ) (hf : ∀ i, ¬ Odd i → f i = 0) :
    ∑ i ∈ Finset.range d, f i = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, f i := by
  unfold Formalism.IncomingBounds.oddLevels
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · exact hf i h

/- English proof (translation)
Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, h0, h1, h2, rfl⟩`. Establish `e : ∀ s, ∑ i ∈ Finset.range d, x s i = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, x s i` using `fun s => sum_range_eq d _ fun i hi => h1 s i (Or.inl hi)`. Use `⟨x, ⟨h0, fun s => ?_⟩, ?_⟩` and prove the remaining obligations.

Use `h2 s` as an intermediate fact. Rewrite `this` using `[sum_range_eq d _ fun i hi => by rw [h1 s i (Or.inl hi), mul_zero], sum_range_eq d (fun i => x (s - (i : ZMod d)) i) fun i hi => h1 _ i (Or.inl hi)]`. Then use the resulting hypothesis. Simplify using `only [Formalism.IncomingBounds.flowVal, e]`. Introduce and unpack `⟨x, ⟨h0, h2⟩, rfl⟩`. Use `⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s i dsimp only split_ifs`. Conclude with `h0 s i`. Conclude with `le_rfl`. Introduce `s i h`. Establish `: ¬ (Odd i ∧ i < d)`.

Introduce and unpack `⟨a, b⟩`. Break down `h with h | h` into its components or cases. Conclude with `h a`. Use linear arithmetic over natural numbers and integers. Simplify using `only [this, if_false]`.

Introduce `s`. Simplify using `only [mul_ite, mul_zero]`. Rewrite using `[sum_range_ite, sum_range_ite]`. Conclude with `h2 s`. Simplify using `only [Formalism.IncomingBounds.flowVal, sum_range_ite]`.
-/
lemma lpFeasible_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) :
    lpFeasible l d D = {t : ℝ | ∃ x, Formalism.IncomingBounds.IsFlow l d D x ∧ Formalism.IncomingBounds.flowVal d x = t} := by
  ext t
  constructor
  · rintro ⟨x, h0, h1, h2, rfl⟩
    have e : ∀ s, ∑ i ∈ Finset.range d, x s i = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, x s i :=
      fun s => sum_range_eq d _ fun i hi => h1 s i (Or.inl hi)
    refine ⟨x, ⟨h0, fun s => ?_⟩, ?_⟩
    · have := h2 s
      rwa [sum_range_eq d _ fun i hi => by rw [h1 s i (Or.inl hi), mul_zero],
        sum_range_eq d (fun i => x (s - (i : ZMod d)) i) fun i hi => h1 _ i (Or.inl hi)] at this
    · simp only [Formalism.IncomingBounds.flowVal, e]
  · rintro ⟨x, ⟨h0, h2⟩, rfl⟩
    refine ⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩
    · intro s i
      dsimp only
      split_ifs
      · exact h0 s i
      · exact le_rfl
    · intro s i h
      have : ¬ (Odd i ∧ i < d) := by
        rintro ⟨a, b⟩
        rcases h with h | h
        · exact h a
        · omega
      simp only [this, if_false]
    · intro s
      simp only [mul_ite, mul_zero]
      rw [sum_range_ite, sum_range_ite]
      exact h2 s
    · simp only [Formalism.IncomingBounds.flowVal, sum_range_ite]

/- English proof (translation)
Unfold `lpF Formalism.IncomingBounds.Fnum Formalism.IncomingBounds.maxFlow Formalism.IncomingBounds.gam`. Rewrite using `[lpFeasible_eq]`.
-/
lemma lpF_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) : lpF l d D = Formalism.IncomingBounds.Fnum l d D := by
  unfold lpF Formalism.IncomingBounds.Fnum Formalism.IncomingBounds.maxFlow Formalism.IncomingBounds.gam
  rw [lpFeasible_eq]

/- English proof (translation)
Introduce `l d _ hl hd _ D _ hD`. Establish `hl' : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hp : (0 : ℝ) < l + 1` using `by linarith`. Establish `hg : IsGreatest (lpFeasible l d D) ((∑ a, D a) / ((l : ℝ) + 1))`. Prove the components needed by the constructor for the conclusion.

Take `⟨x, ⟨h0, h1, h2⟩, h3⟩` from `GlobalTheory.FlowProgramme.balanced l d D hl hd (fun a b => hD b a)`. Use `⟨x, h0, fun s i h => ?_, h2, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Take `⟨a, b⟩` from `h1 s i hc`. Break down `h with h | h` into its components or cases.

Conclude with `h a`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← h3]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `t ⟨x, h0, h1, h2, rfl⟩`.

Use `(GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1` as an intermediate fact. Rewrite using `[le_div_iff₀ hp]`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hc`. Use `h (h1 a i ?_)` and prove the remaining obligations.

Distinguish the cases in `ho : Odd i`. Conclude with `Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)`. Conclude with `Or.inl ho`. Rewrite using `[← lpF_eq]`. Unfold `lpF`.

Rewrite using `[hg.csSup_eq]`. Establish `h1 : (l : ℝ) - 1 ≠ 0` using `by linarith`. Establish `h2 : (l : ℝ) ^ 2 - 1 = (l - 1) * (l + 1)` using `by ring`. Use `show _ = 1 / ((l : ℝ) ^ 2 - 1) * _`. Rewrite using `[h2]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lemmaFe : LemmaFe := by
  intro l d _ hl hd _ D _ hD
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hp : (0 : ℝ) < l + 1 := by linarith
  have hg : IsGreatest (lpFeasible l d D) ((∑ a, D a) / ((l : ℝ) + 1)) := by
    constructor
    · obtain ⟨x, ⟨h0, h1, h2⟩, h3⟩ :=
        GlobalTheory.FlowProgramme.balanced l d D hl hd (fun a b => hD b a)
      refine ⟨x, h0, fun s i h => ?_, h2, ?_⟩
      · by_contra hc
        obtain ⟨a, b⟩ := h1 s i hc
        rcases h with h | h
        · exact h a
        · omega
      · rw [← h3]; field_simp
    · rintro t ⟨x, h0, h1, h2, rfl⟩
      have := (GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1
      · rw [le_div_iff₀ hp]; linarith
      · by_contra hc
        refine h (h1 a i ?_)
        by_cases ho : Odd i
        · exact Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)
        · exact Or.inl ho
  rw [← lpF_eq]
  unfold lpF
  rw [hg.csSup_eq]
  have h1 : (l : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (l : ℝ) ^ 2 - 1 = (l - 1) * (l + 1) := by ring
  show _ = 1 / ((l : ℝ) ^ 2 - 1) * _
  rw [h2]
  field_simp
  ring

/- English proof (translation)
Unfold `NumDatum.pos`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `only`. Apply the tactic sequence `by_cases h : N.cls l = PrimeClass.signal <;> by_cases hs : Odd s <;> by_cases ht : Odd t <;>`. Simplify using `[h, hs, ht, Nat.odd_add, ← Nat.not_odd_iff_even]`.

Simplify using `only`. Rewrite using `[add_smul, add_assoc]`.
-/
lemma pos_add (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ℕ) :
    N.pos l (N.pos l z s) t = N.pos l z (s + t) := by
  unfold NumDatum.pos
  refine Prod.ext ?_ ?_
  · dsimp only
    by_cases h : N.cls l = PrimeClass.signal <;> by_cases hs : Odd s <;> by_cases ht : Odd t <;>
      simp [h, hs, ht, Nat.odd_add, ← Nat.not_odd_iff_even]
  · dsimp only
    rw [add_smul, add_assoc]

/- English proof (translation)
Unfold `NumDatum.pos NumDatum.ordP`. Distinguish the cases in `h : N.cls l = PrimeClass.signal`. Rewrite using `[if_pos h]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `: ¬ Odd (2 * addOrderOf (2 • N.hP l) * c)`.

Rewrite using `[Nat.not_odd_iff_even, mul_assoc]`. Conclude with `even_two_mul _`. Simplify using `only`. Rewrite using `[decide_eq_false (fun hh => this hh.2), Bool.xor_false]`. Simplify using `only`.

Rewrite using `[show 2 * addOrderOf (2 • N.hP l) * c = c * addOrderOf (2 • N.hP l) * 2 by ring, mul_smul, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]`. Rewrite using `[if_neg h]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[h]`. Simplify using `only`.

Rewrite using `[mul_comm, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]`.
-/
lemma pos_mul_period (N : NumDatum) (l : ℕ) (z : RPl N.R) (c : ℕ) :
    N.pos l z (N.ordP l * c) = z := by
  unfold NumDatum.pos NumDatum.ordP
  by_cases h : N.cls l = PrimeClass.signal
  · rw [if_pos h]
    refine Prod.ext ?_ ?_
    · have : ¬ Odd (2 * addOrderOf (2 • N.hP l) * c) := by
        rw [Nat.not_odd_iff_even, mul_assoc]; exact even_two_mul _
      dsimp only
      rw [decide_eq_false (fun hh => this hh.2), Bool.xor_false]
    · dsimp only
      rw [show 2 * addOrderOf (2 • N.hP l) * c = c * addOrderOf (2 • N.hP l) * 2 by ring,
        mul_smul, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]
  · rw [if_neg h]
    refine Prod.ext ?_ ?_
    · simp [h]
    · dsimp only
      rw [mul_comm, mul_smul, addOrderOf_nsmul_eq_zero, smul_zero, add_zero]

/- English proof (translation)
Use `conv_rhs => rw [← Nat.div_add_mod e (N.ordP l), ← pos_add, pos_mul_period]`.
-/
lemma pos_mod (N : NumDatum) (l : ℕ) (z : RPl N.R) (e : ℕ) :
    N.pos l z (e % N.ordP l) = N.pos l z e := by
  conv_rhs => rw [← Nat.div_add_mod e (N.ordP l), ← pos_add, pos_mul_period]

/- English proof (translation)
Unfold `NumDatum.FOrb`. Rewrite using `[← lpF_shift l (N.ordP l) (fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) c]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[pos_add, ZMod.val_add, pos_mod, add_comm]`.
-/
lemma FOrb_step (N : NumDatum) (j l : ℕ) (z : RPl N.R) (c : ZMod (N.ordP l)) :
    N.FOrb j l (N.pos l z c.val) = N.FOrb j l z := by
  unfold NumDatum.FOrb
  rw [← lpF_shift l (N.ordP l) (fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) c]
  congr 1
  funext s
  rw [pos_add, ZMod.val_add, pos_mod, add_comm]

/- English proof (translation)
Rewrite using `[← Finset.sum_product']`. Use `symm`. Use `Finset.sum_bij (fun p _ => N.pos l p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `p hp q hq h`. Conclude with `(hZ _).unique ⟨(Finset.mem_product.1 hp).1, h⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩`.

Introduce `z _`. Take `⟨p, hp, -⟩` from `hZ z`. Conclude with `⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩`.
-/
lemma sum_reps (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (hZ : IsReps N l Z)
    (f : RPl N.R → ℝ) :
    ∑ z, f z = ∑ z ∈ Z, ∑ s : ZMod (N.ordP l), f (N.pos l z s.val) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => N.pos l p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro p hp q hq h
    exact (hZ _).unique ⟨(Finset.mem_product.1 hp).1, h⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := hZ z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

/- English proof (translation)
Introduce `N j l Z hZ hc hn`. Prove the components needed by the constructor for the conclusion. Unfold `NumDatum.FInert`. Rewrite using `[if_neg hn, sum_reps N l Z hZ]`. Establish `hd : (N.ordP l : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne _)`.

Simplify using `only [FOrb_step, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]`. Rewrite using `[← Finset.mul_sum, mul_div_cancel_left₀ _ hd]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Unfold `NumDatum.FOrb alongOrb`. Conclude with `lpF_eq _ _ _`.

Introduce `h0 h1 hX`. Unfold `NumDatum.FjP`. Establish `hr : N.cls l ≠ PrimeClass.ramD`. Apply the tactic sequence `rcases hc with h | h <;> rw [h] <;> simp`. Rewrite using `[if_neg (by tauto), if_neg hr, if_pos ⟨hc, hX⟩]`.
-/
theorem fInertReps : FInertReps := by
  intro N j l Z hZ hc hn
  constructor
  · unfold NumDatum.FInert
    rw [if_neg hn, sum_reps N l Z hZ]
    have hd : (N.ordP l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
    simp only [FOrb_step, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hd]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold NumDatum.FOrb alongOrb
    exact lpF_eq _ _ _
  · intro h0 h1 hX
    unfold NumDatum.FjP
    have hr : N.cls l ≠ PrimeClass.ramD := by
      rcases hc with h | h <;> rw [h] <;> simp
    rw [if_neg (by tauto), if_neg hr, if_pos ⟨hc, hX⟩]

/- English proof (translation)
Assemble the required witnesses or components as `⟨thlEq, levelBound, lemmaFe, fInertReps⟩`.
-/
theorem main : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps :=
  ⟨thlEq, levelBound, lemmaFe, fInertReps⟩

end GlobalTheory.LevelsOrbits
