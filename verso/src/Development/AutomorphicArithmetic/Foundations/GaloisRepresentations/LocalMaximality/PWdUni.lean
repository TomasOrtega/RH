import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {β κ : Type} [LinearOrder β] [LinearOrder κ]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.
-/
private theorem lex_cases (t : β ⊕ₗ κ) : (∃ i, t = inlE i) ∨ ∃ l, t = inrE l := by
  rcases t with i | l
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem mem_uni_l (b : Finset β) (L : Finset κ) (i : β) :
    (inlE i : β ⊕ₗ κ) ∈ uni b L ↔ i ∈ b := by
  simp [uni, inlE]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem mem_uni_r (b : Finset β) (L : Finset κ) (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ uni b L ↔ l ∈ L := by
  simp [uni, inrE]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem mem_lft (s : Finset (β ⊕ₗ κ)) (i : β) : i ∈ lft s ↔ (inlE i : β ⊕ₗ κ) ∈ s := by
  simp [lft, inlE]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem mem_rgt (s : Finset (β ⊕ₗ κ)) (l : κ) : l ∈ rgt s ↔ (inrE l : β ⊕ₗ κ) ∈ s := by
  simp [rgt, inrE]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem l_lt_r (i : β) (l : κ) : (inlE i : β ⊕ₗ κ) < inrE l := Sum.Lex.inl_lt_inr i l

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem not_r_lt_l (i : β) (l : κ) : ¬ (inrE l : β ⊕ₗ κ) < inlE i := Sum.Lex.not_inr_lt_inl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem card_uni (b : Finset β) (L : Finset κ) : (uni b L).card = b.card + L.card := by
  simp [uni]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem sum_uni {M : Type} [AddCommMonoid M] (b : Finset β) (L : Finset κ) (f : β ⊕ₗ κ → M) :
    ∑ t ∈ uni b L, f t = ∑ i ∈ b, f (inlE i) + ∑ l ∈ L, f (inrE l) := by
  rw [uni, Finset.sum_map, Finset.sum_disjSum]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem erase_l [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (i : β) :
    (uni b L).erase (inlE i) = uni (b.erase i) L := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l, Finset.mem_erase, inlE.injective.ne_iff]
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r]
    exact and_iff_right (l_lt_r i m).ne'

/- English proof (translation)
By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem erase_r [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (l : κ) :
    (uni b L).erase (inrE l) = uni b (L.erase l) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l]
    exact and_iff_right (l_lt_r j l).ne
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r, Finset.mem_erase, inrE.injective.ne_iff]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem sign_l (b : Finset β) (L : Finset κ) (i : β) :
    GlobalTheory.cubeSign (uni b L) (inlE i) = GlobalTheory.cubeSign b i := by
  unfold GlobalTheory.cubeSign
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [not_r_lt_l]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem sign_r (b : Finset β) (L : Finset κ) (l : κ) :
    GlobalTheory.cubeSign (uni b L) (inrE l) = (-1 : ℤ) ^ b.card * GlobalTheory.cubeSign L l := by
  unfold GlobalTheory.cubeSign
  rw [← pow_add]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [l_lt_r]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem wd_app {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.productCup_of_system.wdUni_of :
    WdUni := by
  intro β κ E _ _ _ _ w c b L
  refine ⟨?_, ?_, ?_, card_uni b L, ?_⟩
  · rw [wd_app, wd_app, wd_app, sum_uni, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [sign_l, erase_l]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [sign_r, erase_r, mul_smul]
  · ext i
    rw [mem_lft, mem_uni_l]
  · ext l
    rw [mem_rgt, mem_uni_r]
  · intro s
    ext t
    rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · rw [mem_uni_l, mem_lft]
    · rw [mem_uni_r, mem_rgt]
