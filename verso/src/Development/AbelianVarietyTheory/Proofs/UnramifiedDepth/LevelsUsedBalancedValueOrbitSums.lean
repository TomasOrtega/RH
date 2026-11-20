import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Formalism.LocalRingCardinality.DataForced
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CyclicSolvable

open Formalism.L2.FormalSeriesBounds Formalism.L2.DIV Formalism.BasicNotions Formalism.UnitaryBoundIntegral

namespace GlobalTheory.LevelsOrbits

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
lemma levels_nonempty (k l : ℕ) (hl : 2 ≤ l) :
    {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}.Nonempty := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((k : ℝ) ^ ((3 : ℝ) / 2)) (show (1 : ℝ) < l by linarith)
  refine ⟨2 * n + 3, ⟨n + 1, by ring⟩, by omega, hn.trans_le ?_⟩
  exact pow_le_pow_right₀ (by linarith) (by omega)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
lemma sum_range_ite (d : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then f i else 0) = ∑ i ∈ Formalism.IncomingBounds.oddLevels d, f i := by
  unfold Formalism.IncomingBounds.oddLevels
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Finset.mem_range.1 hi]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Separate the alternatives or extract the components of the hypothesis. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma lpF_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) : lpF l d D = Formalism.IncomingBounds.Fnum l d D := by
  unfold lpF Formalism.IncomingBounds.Fnum Formalism.IncomingBounds.maxFlow Formalism.IncomingBounds.gam
  rw [lpFeasible_eq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Prove the second alternative. Prove the first alternative. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.
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
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
lemma pos_mod (N : NumDatum) (l : ℕ) (z : RPl N.R) (e : ℕ) :
    N.pos l z (e % N.ordP l) = N.pos l z e := by
  conv_rhs => rw [← Nat.div_add_mod e (N.ordP l), ← pos_add, pos_mul_period]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
lemma FOrb_step (N : NumDatum) (j l : ℕ) (z : RPl N.R) (c : ZMod (N.ordP l)) :
    N.FOrb j l (N.pos l z c.val) = N.FOrb j l z := by
  unfold NumDatum.FOrb
  rw [← lpF_shift l (N.ordP l) (fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) c]
  congr 1
  funext s
  rw [pos_add, ZMod.val_add, pos_mod, add_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Supply the required witnesses or components.
-/
theorem main : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps :=
  ⟨thlEq, levelBound, lemmaFe, fInertReps⟩

end GlobalTheory.LevelsOrbits
