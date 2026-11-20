import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PrinSumP

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)

variable {A : Type*} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Substitute using the available equality. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Proceed by induction. Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem prod_ofFn_sub : ∀ (m : ℕ) (f g : Fin (m + 1) → A) (d : Fin (m + 1)),
    (∀ j, j ≠ d → f j = g j) → f d = g d + 1 →
    (List.ofFn f).prod - (List.ofFn g).prod = (List.ofFn (f ∘ d.succAbove)).prod := by
  intro m
  induction m with
  | zero =>
    intro f g d _ hd
    have hd0 : d = 0 := Fin.fin_one_eq_zero d
    subst hd0
    simp [hd]
  | succ m ih =>
    intro f g d h hd
    rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g), List.prod_cons, List.prod_cons]
    induction d using Fin.cases with
    | zero =>
      have ht : (fun i : Fin (m + 1) => f i.succ) = fun i => g i.succ :=
        funext fun i => h _ (Fin.succ_ne_zero i)
      rw [ht, hd, add_mul, one_mul, add_sub_cancel_left]
      congr 2
      funext i
      simp [ht, congrFun ht i]
    | succ e =>
      have h0 : f 0 = g 0 := h 0 (Fin.succ_ne_zero e).symm
      have key := ih (fun i => f i.succ) (fun i => g i.succ) e
        (fun j hj => h _ (fun hh => hj (Fin.succ_injective _ hh))) hd
      rw [← h0, ← mul_sub, key, List.ofFn_succ, List.prod_cons]
      congr 2
      simp [Function.comp_def, Fin.succ_succAbove_succ]

def colDet {n : ℕ} (E : Fin n → Fin n → A) (c : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin n => capEntry E (c j) (σ j) j).prod

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Tm_eq_capEntry {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    Tm E u a b = capEntry E u a b := add_comm _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
theorem qdet_eq_colDet {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    qdet E u = colDet E (fun j => u - ((j : ℕ) : ℂ)) := by
  unfold qdet qminor colDet
  refine sum_congr rfl fun σ _ => ?_
  rw [← zsmul_eq_mul]
  congr 2
  simp only [Tm_eq_capEntry, id]

def ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquiv' d).symm.permCongr (Equiv.Perm.decomposeOption.symm (none, τ))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ins_self {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : ins d τ d = d := by
  simp [ins, Equiv.permCongr_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ins_succAbove {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    ins d τ (d.succAbove i) = d.succAbove (τ i) := by
  simp [ins, Equiv.permCongr_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sign_ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ins d τ) = Equiv.Perm.sign τ := by
  simp [ins, Equiv.Perm.decomposeOption_symm_sign]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ins_injective {m : ℕ} (d : Fin (m + 1)) : Function.Injective (ins d) := by
  intro τ τ' h
  ext i
  have := congrArg (fun s : Equiv.Perm (Fin (m + 1)) => s (d.succAbove i)) h
  simp only [ins_succAbove] at this
  exact congrArg Fin.val (Fin.succAbove_right_injective this)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_ins {m : ℕ} (d : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) (h : σ d = d) :
    ∃ τ, ins d τ = σ := by
  set s : Equiv.Perm (Option (Fin m)) := (finSuccEquiv' d).permCongr σ with hs
  have hnone : s none = none := by
    simp [hs, Equiv.permCongr_apply, h]
  obtain ⟨⟨o, τ⟩, hq⟩ := Equiv.Perm.decomposeOption.symm.surjective s
  have ho : o = none := by
    rw [← hnone, ← hq]
    simp
  subst ho
  refine ⟨τ, ?_⟩
  unfold ins
  rw [hq, hs]
  ext x
  simp [Equiv.permCongr_apply]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem colDet_sub {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (c c' : Fin (m + 1) → ℂ)
    (d : Fin (m + 1)) (h : ∀ j, j ≠ d → c j = c' j) (hd : c d = c' d + 1) :
    colDet E c - colDet E c' = ∑ τ : Equiv.Perm (Fin m), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      (List.ofFn fun i : Fin m =>
        capEntry E (c (d.succAbove i)) (d.succAbove (τ i)) (d.succAbove i)).prod := by
  have each : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c j) (σ j) j).prod -
        ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c' j) (σ j) j).prod =
      if σ d = d then ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (List.ofFn ((fun j => capEntry E (c j) (σ j) j) ∘ d.succAbove)).prod else 0 := by
    intro σ
    rw [← smul_sub]
    split_ifs with hσ
    · rw [prod_ofFn_sub m _ (fun j => capEntry E (c' j) (σ j) j) d]
      · intro j hj
        simp only [h j hj]
      · simp only [capEntry, hσ, if_true, hd, map_add, map_one]
        abel
    · have : (fun j => capEntry E (c j) (σ j) j) = fun j => capEntry E (c' j) (σ j) j := by
        funext j
        by_cases hj : j = d
        · subst hj
          simp [capEntry, hσ]
        · simp only [h j hj]
      rw [this, sub_self, smul_zero]
  unfold colDet
  rw [← sum_sub_distrib, sum_congr rfl fun σ _ => each σ, ← sum_filter]
  symm
  refine sum_bij (fun τ _ => ins d τ) ?_ ?_ ?_ ?_
  · intro τ _
    simp [ins_self]
  · intro τ _ τ' _ hh
    exact ins_injective d hh
  · intro σ hσ
    obtain ⟨τ, rfl⟩ := exists_ins d σ (by simpa using hσ)
    exact ⟨τ, mem_univ _, rfl⟩
  · intro τ _
    rw [sign_ins]
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    simp [ins_succAbove]

def hyb {n : ℕ} (x : ℂ) (k : ℕ) (j : Fin n) : ℂ :=
  if (j : ℕ) < k then x - 1 - ((j : ℕ) : ℂ) else x - ((j : ℕ) : ℂ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hyb_step {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) (d : Fin (m + 1)) :
    colDet E (hyb x (d : ℕ)) - colDet E (hyb x ((d : ℕ) + 1)) =
      cminor E d.succAbove d.succAbove (x - 1) := by
  rw [colDet_sub E _ _ d]
  · unfold cminor
    refine sum_congr rfl fun τ _ => ?_
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    congr 1
    unfold hyb
    rcases lt_or_ge (i : ℕ) (d : ℕ) with hi | hi
    · have e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hi)]
        simp
      rw [e, if_pos hi]
    · have e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hi)]
        simp
      rw [e, if_neg (by omega)]
      push_cast
      ring
  · intro j hj
    have : (j : ℕ) ≠ d := fun hh => hj (Fin.ext hh)
    unfold hyb
    by_cases h1 : (j : ℕ) < d
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · unfold hyb
    rw [if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
    ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem sum_principal {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) :
    ∑ d : Fin (m + 1), cminor E d.succAbove d.succAbove (x - 1) = qdet E x - qdet E (x - 1) := by
  have h0 : qdet E x = colDet E (hyb x 0) := by
    rw [qdet_eq_colDet]
    congr 1
  have h1 : qdet E (x - 1) = colDet E (hyb x (m + 1)) := by
    rw [qdet_eq_colDet]
    congr 1
    funext j
    simp [hyb, j.2]
  rw [h0, h1, ← sum_congr rfl fun d _ => hyb_step E x d,
    Fin.sum_univ_eq_sum_range (fun k => colDet E (hyb x k) - colDet E (hyb x (k + 1))) (m + 1),
    sum_range_sub']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem prinSum : CompanionTheory.RgExh.Hk.PrinSum := by
  intro m M _ _ E _ x
  exact sum_principal E x

end GlobalTheory.CompanionTheory.PrinSumP
