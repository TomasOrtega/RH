import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsDef
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColOKOfPath

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Use linear arithmetic over natural numbers and integers. Move the embeddings inside the algebraic operations. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem strip_count {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) (h : HStrip nu mu b) (S : Finset ℤ)
    (hS : ∀ a c, nu a < c → c ≤ mu a → c ∈ S) :
    (S.filter fun c => colH nu c ≠ colH mu c).card = b := by
  classical
  have h1 : ∀ c, ((if colH nu c ≠ colH mu c then 1 else 0 : ℕ) : ℤ) =
      ∑ a : Fin n, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0) := by
    intro c
    obtain ⟨l1, l2⟩ := colH_strip nu mu b h c
    have e : (colH mu c : ℤ) - colH nu c = ∑ a : Fin n, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0) := by
      unfold colH
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := h.1 a
      by_cases c1 : c ≤ mu a <;> by_cases c2 : c ≤ nu a
      · rw [if_pos c1, if_pos c2, if_neg (by omega)]; ring
      · rw [if_pos c1, if_neg c2, if_pos (by omega)]; ring
      · omega
      · rw [if_neg c1, if_neg c2, if_neg (by omega)]; ring
    rw [← e]
    split_ifs with hne
    · push_cast; omega
    · push_cast; omega
  have h2 : ((S.filter fun c => colH nu c ≠ colH mu c).card : ℤ) = b := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm, ← h.2.2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : S.filter (fun c => nu a < c ∧ c ≤ mu a) = Finset.Ioc (nu a) (mu a) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨fun x => x.2, fun x => ⟨hS a c x.1 x.2, x⟩⟩
    have e2 : (∑ c ∈ S, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0)) =
        ((S.filter (fun c => nu a < c ∧ c ≤ mu a)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [e2, e, Int.card_Ioc]
    have := h.1 a
    omega
  exact_mod_cast h2

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem sum_range_odd {M : Type*} [AddCommMonoid M] (G : ℕ → M) (s : ℕ) :
    ∑ a ∈ Finset.range (2 * s + 1), G a = (∑ l ∈ Finset.range s, (G (2 * l) + G (2 * l + 1))) + G (2 * s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : 2 * (s + 1) + 1 = (2 * s + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e2 : 2 * (s + 1) = 2 * s + 1 + 1 := by ring
    rw [e2]
    abel

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_fin_odd {M : Type*} [AddCommMonoid M] (s : ℕ) (F : Fin (2 * s + 1) → M) :
    ∑ a, F a = (∑ l : Fin s, (F ⟨2 * l.val, by have := l.2; omega⟩ + F ⟨2 * l.val + 1, by have := l.2; omega⟩)) +
      F ⟨2 * s, by omega⟩ := by
  classical
  set G : ℕ → M := fun a => if h : a < 2 * s + 1 then F ⟨a, h⟩ else 0 with hG
  have e1 : ∑ a, F a = ∑ a ∈ Finset.range (2 * s + 1), G a := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hG]; simp only [a.2, dif_pos]
  rw [e1, sum_range_odd, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    have := l.2
    rw [hG]
    simp only
    rw [dif_pos (by omega), dif_pos (by omega)]
  · rw [hG]; simp only; rw [dif_pos (by omega)]

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
