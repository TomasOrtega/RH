import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem rearr_gap (n : ℕ) (a b : Fin n) : rhoV n a - rhoV n b = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
  simp only [rhoV]
  ring

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem sum_mul_perm_le_and_eq_one_of_antitone {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y) (w : Equiv.Perm (Fin n)) :
    ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
      (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1) := by
  have hm : Monovary x y := hx.monovary hy
  refine ⟨hm.sum_mul_comp_perm_le_sum_mul, fun sx sy he => ?_⟩
  have h2 := hm.sum_mul_comp_perm_eq_sum_mul_iff.1 he
  have hmono : StrictMono w := by
    intro i j hij
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hlt | heq
    · exact absurd (h2 (show y (w i) < y (w j) from sy hlt)) (not_le.2 (sx hij))
    · exact absurd (w.injective heq) (ne_of_gt hij)
  have := hmono.eq_id
  ext i
  simp [this]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem rearr_lemma_2 {n : ℕ} (x : Fin n → ℝ) :
    Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
      (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x := by
  refine ⟨?_, ⟨_, rfl⟩, fun hx => ?_, fun w => ?_, ?_⟩
  · intro a b hab
    have := Tuple.monotone_sort (fun a => -x a) hab
    simpa [domC] using this
  · have : Tuple.sort (fun a => -x a) = Equiv.refl (Fin n) :=
      Tuple.sort_eq_refl_iff_monotone.2 (fun a b hab => neg_le_neg (hx hab))
    simp [domC, this]
  · have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := fun a => -x a) (σ := w)
    funext a
    show (x ∘ w) ((Tuple.sort ((fun a => -x a) ∘ w)) a) = x ((Tuple.sort fun a => -x a) a)
    have := congrFun h a
    simp only [Function.comp_apply, neg_inj] at this
    exact this
  · unfold nsq domC
    exact Equiv.sum_comp (Tuple.sort fun a => -x a) (fun a => x a ^ 2)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Replace the relevant objects with their definitions.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem strictAnti_rhoV_and_dom_rhoV (n : ℕ) : StrictAnti (rhoV n) ∧ Dom (rhoV n) := by
  constructor
  · intro a b hab
    have h1 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith [rearr_gap n a b]
  · unfold Dom
    intro a b hab
    refine ⟨(b : ℕ) - (a : ℕ), ?_⟩
    rw [rearr_gap, Nat.cast_sub (Fin.lt_def.mp hab).le]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
private theorem antitone_and_dom_domC_sub_rhoV_of_dom (n : ℕ) (x : Wt n) (hx : Dom x) : Antitone x ∧ Dom (domC (x - rhoV n)) := by
  unfold Dom at hx
  have hint : ∀ a b, ∃ k : ℤ, (x - rhoV n) a - (x - rhoV n) b = k := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨m, hm⟩ := hx a b h
      refine ⟨(m : ℤ) - ((b : ℕ) : ℤ) + ((a : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n a b]
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨m, hm⟩ := hx b a h
      refine ⟨-(m : ℤ) + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply]
      push_cast
      linarith [rearr_gap n b a]
  refine ⟨fun a b hab => ?_, ?_⟩
  · rcases hab.lt_or_eq with h | h
    · obtain ⟨m, hm⟩ := hx a b h
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · rw [h]
  · unfold Dom
    intro a b hab
    obtain ⟨w, hw⟩ := (rearr_lemma_2 (x - rhoV n)).2.1
    have hanti := (rearr_lemma_2 (x - rhoV n)).1
    obtain ⟨k, hk⟩ := hint (w a) (w b)
    have hk0 : (0 : ℝ) ≤ k := by
      have := hanti hab.le
      rw [hw] at this
      simp only [Function.comp_apply] at this
      linarith
    have hk1 : (0 : ℤ) ≤ k := by exact_mod_cast hk0
    refine ⟨k.toNat, ?_⟩
    rw [hw]
    simp only [Function.comp_apply]
    rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg hk1]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem nsq_le_and_eq_of_nsq_le_sum_mul {n : ℕ} (x y : Fin n → ℝ) (h : nsq x ≤ ∑ a, x a * y a) :
    nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  have hsq : 0 ≤ ∑ a, (x a - y a) ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hexp : ∑ a, (x a - y a) ^ 2 = nsq x - 2 * ∑ a, x a * y a + nsq y := by
    unfold nsq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine ⟨by linarith, fun h2 => ?_⟩
  have h0 : ∑ a, (x a - y a) ^ 2 = 0 := by linarith
  funext a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (x a - y a))).1 h0 a (Finset.mem_univ a)
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem UpperTheory.RealTr.rearr :
    ∀ n : ℕ, (∀ x y : Wt n, Antitone x → Antitone y → ∀ w : Equiv.Perm (Fin n), ∑ a, x a * y (w a) ≤ ∑ a, x a * y a ∧
        (StrictAnti x → StrictAnti y → ∑ a, x a * y (w a) = ∑ a, x a * y a → w = 1)) ∧
      (∀ x : Wt n, Antitone (domC x) ∧ (∃ w : Equiv.Perm (Fin n), domC x = x ∘ w) ∧ (Antitone x → domC x = x) ∧
        (∀ w : Equiv.Perm (Fin n), domC (x ∘ w) = domC x) ∧ nsq (domC x) = nsq x) ∧
      StrictAnti (rhoV n) ∧ Dom (rhoV n) ∧ (∀ x : Wt n, Dom x → Antitone x ∧ Dom (domC (x - rhoV n))) ∧
      ∀ x y : Wt n, nsq x ≤ ∑ a, x a * y a → nsq x ≤ nsq y ∧ (nsq y ≤ nsq x → x = y) := by
  intro n
  exact ⟨fun x y hx hy w => sum_mul_perm_le_and_eq_one_of_antitone x y hx hy w, fun x => rearr_lemma_2 x, (strictAnti_rhoV_and_dom_rhoV n).1, (strictAnti_rhoV_and_dom_rhoV n).2,
    fun x hx => antitone_and_dom_domC_sub_rhoV_of_dom n x hx, fun x y h => nsq_le_and_eq_of_nsq_le_sum_mul x y h⟩
