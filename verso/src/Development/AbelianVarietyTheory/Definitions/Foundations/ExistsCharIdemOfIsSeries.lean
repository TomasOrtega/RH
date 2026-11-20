import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare.Basic

section Central
variable {G : Type} [Group G] [Fintype G]

end Central

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Unfold `IsUp IsUniUp`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ a b`. Use `⟨h2 a b, fun hab => ?_⟩` and prove the remaining obligations. Substitute `hab` using the available equality.

Conclude with `h1 a`. Introduce `h`. Conclude with `⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩`.
-/
theorem isUp_iff_isUniUp (u : GG g N) : IsUp g N u ↔ IsUniUp u.val := by
  unfold IsUp IsUniUp
  constructor
  · rintro ⟨h1, h2⟩ a b
    refine ⟨h2 a b, fun hab => ?_⟩
    subst hab
    exact h1 a
  · intro h
    exact ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

open Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Unfold `eDat eps`. Simplify using `only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use `split_ifs`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_inv_mul]`. Simplify using the standard rewrite rules.
-/
theorem coeff_eDat (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (x : GG g N) :
    (eDat g N P φ ψ).coeff x = eps (fun u : GG g N => P u.val) (fun u => ψ (φ u.val)) x := by
  classical
  unfold eDat eps
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_inv_mul]
  · simp

open Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Unfold `entN`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨c, h.2⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Introduce `hbc`. Conclude with `hb (Fin.ext hbc)`. Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b _`. Rewrite using `[if_neg]`. Introduce `hbc`. Conclude with `h ⟨a.isLt, hbc ▸ b.isLt⟩`.
-/
theorem sum_ite_entN (M : Matrix (Fin N) (Fin N) (ZMod g)) (a : Fin N) (c : ℕ) :
    (∑ b : Fin N, if (b : ℕ) = c then M a b else 0) = entN M a c := by
  unfold entN
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c, h.2⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbc
      exact hb (Fin.ext hbc)
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbc
    exact h ⟨a.isLt, hbc ▸ b.isLt⟩

/- English proof (translation)
Simplify using `only [sum_ite_entN]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN M i (i + 1)) N]`. Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Rewrite using `[Finset.sum_range_succ, Nat.add_sub_cancel, show Formalism.MainNotions.ArithmeticCylinders.entN M n (n + 1) = 0 by unfold Formalism.MainNotions.ArithmeticCylinders.entN; rw [dif_neg (by omega)], add_zero]`.
-/
private theorem sum_superdiag_eq_sum_entN (M : Matrix (Fin N) (Fin N) (ZMod g)) (hN : 0 < N) :
    (∑ a : Fin N, ∑ b : Fin N, if (b : ℕ) = a + 1 then M a b else 0) =
      ∑ i ∈ Finset.range (N - 1), Formalism.MainNotions.ArithmeticCylinders.entN M i (i + 1) := by
  simp only [sum_ite_entN]
  rw [Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN M i (i + 1)) N]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.add_sub_cancel,
    show Formalism.MainNotions.ArithmeticCylinders.entN M n (n + 1) = 0 by unfold Formalism.MainNotions.ArithmeticCylinders.entN; rw [dif_neg (by omega)], add_zero]

open Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Establish `hN : 0 < N` using `by omega`. Rewrite using `[eU, coeff_eDat]`. Unfold `levOfChar Lev.e Lev.Mem Lev.chi Lev.Edge`. Simplify using `only [Bool.false_eq_true, ↓reduceIte, false_implies, and_true, isUp_iff_isUniUp, Units.val_one, one_mul, sum_superdiag_eq_sum_entN _ hN]`.
-/
theorem coeff_eU (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (s k : ℕ) (h : s + k < N) (x : GG g N) :
    (eU g N ψ).coeff x = (levOfChar ψ hψ N false s k h).e x := by
  have hN : 0 < N := by omega
  rw [eU, coeff_eDat]
  unfold levOfChar Lev.e Lev.Mem Lev.chi Lev.Edge
  simp only [Bool.false_eq_true, ↓reduceIte, false_implies, and_true, isUp_iff_isUniUp,
    Units.val_one, one_mul, sum_superdiag_eq_sum_entN _ hN]

/- English proof (translation)
Establish `pos : ∀ i, i + 1 ≠ s → ¬(0 < k ∧ i + 1 = s + k) → F i = f i` using `fun i h1 h2 => by`. Rewrite using `[hF, if_pos ⟨h1, h2⟩]`. Establish `neg : ∀ i, ¬(i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k)) → F i = 0` using `fun i h => by`. Rewrite using `[hF, if_neg h]`. Substitute `hN` using the available equality.

Apply the tactic sequence `rcases s with _ | t <;> rcases k with _ | j`. Rewrite using `[show 0 + 2 * 0 + 1 = 1 from rfl, Finset.sum_range_one, pos 0 (by omega) (by omega)]`. Simplify using `using hf`. Rewrite using `[show j + 1 + 2 * 0 + 1 = j + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, neg j (by omega), pos (j + 1) (by omega) (by omega), show f (j + 1) = 0 by simpa using hf]`. Simplify using `only [Nat.zero_sub, Finset.range_zero, Finset.sum_empty, Nat.add_sub_cancel, zero_add, add_zero]`.

Rewrite using `[if_neg (by omega), zero_add]`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `pos i (by omega) (by omega)`. Rewrite using `[show 0 + 2 * (t + 1) + 1 = t + 1 + 1 + t + 1 by omega, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ, neg t (by omega), pos (t + 1) (by omega) (by omega), pos (t + 1 + 1 + t) (by omega) (by omega), show f (t + 1 + 1 + t) = 0 by`.

Rewrite using `[show t + 1 + 1 + t = 0 + 2 * (t + 1) + 1 - 1 by omega]; exact hf]`. Rewrite using `[Nat.add_sub_cancel, if_pos (by omega), Nat.zero_sub, Finset.range_zero, Finset.sum_empty]`. Establish `e1 : ∑ i ∈ Finset.range t, F i = ∑ i ∈ Finset.range t, f i` using `Finset.sum_congr rfl (fun i hi => pos i (by simp at hi; omega) (by omega))`. Establish `e2 : ∑ i ∈ Finset.range t, F (t + 1 + 1 + i) = ∑ i ∈ Finset.range t, f (t + 1 + 0 + 1 + i)` using `Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by omega))`. Rewrite using `[e1, e2]`.

Use `abel_nf`. Rewrite using `[show j + 1 + 2 * (t + 1) + 1 = t + 1 + j + 1 + 1 + t + 1 by omega, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_succ, neg t (by omega), neg (t + 1 + j) (by omega), pos (t + 1 + j + 1) (by omega) …`. Rewrite using `[show t + 1 + j + 1 + 1 + t = j + 1 + 2 * (t + 1) + 1 - 1 by omega]; exact hf]`. Rewrite using `[Nat.add_sub_cancel, Nat.add_sub_cancel, if_pos (by omega)]`. Establish `e1 : ∑ i ∈ Finset.range t, F i = ∑ i ∈ Finset.range t, f i` using `Finset.sum_congr rfl (fun i hi => pos i (by simp at hi; omega) (by simp at hi; omega))`.

Establish `e2 : ∑ i ∈ Finset.range j, F (t + 1 + i) = ∑ i ∈ Finset.range j, f (t + 1 + i)` using `Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by simp at hi; omega))`. Establish `e3 : ∑ i ∈ Finset.range t, F (t + 1 + j + 1 + 1 + i) = ∑ i ∈ Finset.range t, f (t + 1 + (j + 1) + 1 + i)` using `Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by omega))`. Rewrite using `[e1, e2, e3]`. Use `abel_nf`.
-/
private theorem sum_range_eq_sum_split_of_last_eq_zero {R : Type} [AddCommMonoid R] (f F : ℕ → R) (s k N : ℕ) (hN : N = k + 2 * s + 1)
    (hF : ∀ i, F i = if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then f i else 0) (hf : f (N - 1) = 0) :
    ∑ i ∈ Finset.range N, F i = ∑ i ∈ Finset.range (s - 1), f i + (if 1 ≤ s then f (s + k) else 0) +
      ∑ i ∈ Finset.range (s - 1), f (s + k + 1 + i) + ∑ a ∈ Finset.range (k - 1), f (s + a) := by
  have pos : ∀ i, i + 1 ≠ s → ¬(0 < k ∧ i + 1 = s + k) → F i = f i := fun i h1 h2 => by
    rw [hF, if_pos ⟨h1, h2⟩]
  have neg : ∀ i, ¬(i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k)) → F i = 0 := fun i h => by
    rw [hF, if_neg h]
  subst hN
  rcases s with _ | t <;> rcases k with _ | j
  · rw [show 0 + 2 * 0 + 1 = 1 from rfl, Finset.sum_range_one, pos 0 (by omega) (by omega)]
    simpa using hf
  · rw [show j + 1 + 2 * 0 + 1 = j + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      neg j (by omega), pos (j + 1) (by omega) (by omega), show f (j + 1) = 0 by simpa using hf]
    simp only [Nat.zero_sub, Finset.range_zero, Finset.sum_empty, Nat.add_sub_cancel, zero_add, add_zero]
    rw [if_neg (by omega), zero_add]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact pos i (by omega) (by omega)
  · rw [show 0 + 2 * (t + 1) + 1 = t + 1 + 1 + t + 1 by omega, Finset.sum_range_succ, Finset.sum_range_add,
      Finset.sum_range_succ, Finset.sum_range_succ, neg t (by omega), pos (t + 1) (by omega) (by omega),
      pos (t + 1 + 1 + t) (by omega) (by omega), show f (t + 1 + 1 + t) = 0 by
        rw [show t + 1 + 1 + t = 0 + 2 * (t + 1) + 1 - 1 by omega]; exact hf]
    rw [Nat.add_sub_cancel, if_pos (by omega), Nat.zero_sub, Finset.range_zero, Finset.sum_empty]
    have e1 : ∑ i ∈ Finset.range t, F i = ∑ i ∈ Finset.range t, f i :=
      Finset.sum_congr rfl (fun i hi => pos i (by simp at hi; omega) (by omega))
    have e2 : ∑ i ∈ Finset.range t, F (t + 1 + 1 + i) = ∑ i ∈ Finset.range t, f (t + 1 + 0 + 1 + i) :=
      Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by omega))
    rw [e1, e2]
    abel_nf
  · rw [show j + 1 + 2 * (t + 1) + 1 = t + 1 + j + 1 + 1 + t + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_add,
      Finset.sum_range_succ, neg t (by omega), neg (t + 1 + j) (by omega),
      pos (t + 1 + j + 1) (by omega) (by omega), pos (t + 1 + j + 1 + 1 + t) (by omega) (by omega),
      show f (t + 1 + j + 1 + 1 + t) = 0 by
        rw [show t + 1 + j + 1 + 1 + t = j + 1 + 2 * (t + 1) + 1 - 1 by omega]; exact hf]
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, if_pos (by omega)]
    have e1 : ∑ i ∈ Finset.range t, F i = ∑ i ∈ Finset.range t, f i :=
      Finset.sum_congr rfl (fun i hi => pos i (by simp at hi; omega) (by simp at hi; omega))
    have e2 : ∑ i ∈ Finset.range j, F (t + 1 + i) = ∑ i ∈ Finset.range j, f (t + 1 + i) :=
      Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by simp at hi; omega))
    have e3 : ∑ i ∈ Finset.range t, F (t + 1 + j + 1 + 1 + i) =
        ∑ i ∈ Finset.range t, f (t + 1 + (j + 1) + 1 + i) :=
      Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by omega))
    rw [e1, e2, e3]
    abel_nf

open Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Unfold `levOfChar Lev.Edge`. Simplify using `only [↓reduceIte]`. Establish `inner : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) ∨ (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) then M a b else 0) = (if (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) then entN M a (a + 1) else 0) + (if (a : ℕ) + 1 = s then entN M …`. Introduce `a`. Establish `hb : ∀ b : Fin N, (if ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) ∨ (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) then M a b else 0) = (if (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) then (if (b : ℕ) = a + 1 then M a b else 0) else 0) + (if (a : ℕ) + 1 = s then …`.

Introduce `b`. Apply the tactic sequence `by_cases p1 : (b : ℕ) = a + 1 <;> by_cases p2 : (a : ℕ) + 1 = s <;>`. Apply the tactic sequence `by_cases p3 : (0 < k ∧ (a : ℕ) + 1 = s + k) <;> by_cases p4 : (b : ℕ) = s + k <;> simp [p1, p2, p3, p4]`. Rewrite using `[Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_ite_irrel, sum_ite_entN, sum_ite_entN, Finset.sum_const_zero]`. Rewrite using `[Finset.sum_congr rfl (fun a _ => inner a), Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then entN M i (i + 1) else 0) N, Fin.sum_univ_eq_sum_range (fun i => if i + 1 = s then entN M i (s + k) else 0) N, sum_range_eq_sum_spli …`.

Establish `e2 : ∑ i ∈ Finset.range N, (if i + 1 = s then entN M i (s + k) else 0) = if 1 ≤ s then entN M (s - 1) (s + k) else 0`. Break down `s with _ | t` into its components or cases. Rewrite using `[if_neg (by omega)]`. Conclude with `Finset.sum_eq_zero (fun i _ => if_neg (by omega))`. Rewrite using `[if_pos (by omega), Nat.add_sub_cancel]`.

Simplify using `only [Nat.add_right_cancel_iff]`. Rewrite using `[Finset.sum_ite_eq' (Finset.range N) t, if_pos (Finset.mem_range.mpr (by omega))]`. Establish `e3 : ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 1 + i + 1) = ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i)` using `Finset.sum_congr rfl (fun i _ => by rw [show s + k + 1 + i + 1 = s + k + 2 + i by omega])`. Rewrite using `[e2, e3]`. Unfold `phiJ`.

Distinguish the cases in `hs : 1 ≤ s`. Simplify using `only [if_pos hs]`. Normalize the expressions using the abelian group laws. Simplify using `only [if_neg hs]`. Normalize the expressions using the abelian group laws.
-/
theorem sum_edge_eq_phiJ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (s k : ℕ) (hN : N = k + 2 * s + 1) (h : s + k < N)
    (M : Matrix (Fin N) (Fin N) (ZMod g)) :
    (∑ a, ∑ b, if (levOfChar ψ hψ N true s k h).Edge a b then M a b else 0) = phiJ k s M := by
  unfold levOfChar Lev.Edge
  simp only [↓reduceIte]
  have inner : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) ∨
      (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) then M a b else 0) =
      (if (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) then entN M a (a + 1) else 0) +
        (if (a : ℕ) + 1 = s then entN M a (s + k) else 0) := by
    intro a
    have hb : ∀ b : Fin N, (if ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) ∨
        (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) then M a b else 0) =
        (if (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) then (if (b : ℕ) = a + 1 then M a b else 0) else 0) +
          (if (a : ℕ) + 1 = s then (if (b : ℕ) = s + k then M a b else 0) else 0) := by
      intro b
      by_cases p1 : (b : ℕ) = a + 1 <;> by_cases p2 : (a : ℕ) + 1 = s <;>
        by_cases p3 : (0 < k ∧ (a : ℕ) + 1 = s + k) <;> by_cases p4 : (b : ℕ) = s + k <;> simp [p1, p2, p3, p4]
    rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_ite_irrel,
      sum_ite_entN, sum_ite_entN, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun a _ => inner a), Finset.sum_add_distrib,
    Fin.sum_univ_eq_sum_range (fun i => if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then entN M i (i + 1) else 0) N,
    Fin.sum_univ_eq_sum_range (fun i => if i + 1 = s then entN M i (s + k) else 0) N,
    sum_range_eq_sum_split_of_last_eq_zero (fun i => entN M i (i + 1)) (fun i => if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then entN M i (i + 1) else 0)
      s k N hN (fun i => rfl) (by unfold entN; rw [dif_neg (by omega)])]
  have e2 : ∑ i ∈ Finset.range N, (if i + 1 = s then entN M i (s + k) else 0) =
      if 1 ≤ s then entN M (s - 1) (s + k) else 0 := by
    rcases s with _ | t
    · rw [if_neg (by omega)]
      exact Finset.sum_eq_zero (fun i _ => if_neg (by omega))
    · rw [if_pos (by omega), Nat.add_sub_cancel]
      simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq' (Finset.range N) t, if_pos (Finset.mem_range.mpr (by omega))]
  have e3 : ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 1 + i + 1) =
      ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) :=
    Finset.sum_congr rfl (fun i _ => by rw [show s + k + 1 + i + 1 = s + k + 2 + i by omega])
  rw [e2, e3]
  unfold phiJ
  by_cases hs : 1 ≤ s
  · simp only [if_pos hs]
    abel
  · simp only [if_neg hs]
    abel

open Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Rewrite using `[eJ, coeff_eDat]`. Unfold `Lev.e`. Use `congr 1`. Use function extensionality and compare the values at `u`. Unfold `levOfChar Lev.Mem`.

Simplify using `only [isUp_iff_isUniUp, forall_const]`. Apply `propext` to reduce the goal to its premises. Apply `and_congr_right` to reduce the goal to its premises. Introduce `_`. Prove the components needed by the constructor for the conclusion.

Introduce `H a b h1 h2 h3`. Rewrite using `[show b = ⟨s + k, by omega⟩ from Fin.ext h3]`. Use `H a h1 h2` as an intermediate fact. Unfold `entN at this`. Rewrite `this` using `[dif_pos ⟨a.isLt, by omega⟩]`.

Conclude with `this`. Introduce `H a h1 h2`. Unfold `entN`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Conclude with `H ⟨a, by omega⟩ ⟨s + k, by omega⟩ h1 h2 rfl`.

Use function extensionality and compare the values at `u`. Establish `hE` using `sum_edge_eq_phiJ ψ hψ s k hN h (u : Matrix (Fin N) (Fin N) (ZMod g))`. Unfold `levOfChar at hE`. Unfold `levOfChar Lev.chi`. Simplify using `only [Units.val_one, one_mul]`.

Rewrite using `[hE]`.
-/
theorem coeff_eJ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (s k : ℕ) (hN : N = k + 2 * s + 1) (h : s + k < N) (x : GG g N) :
    (eJ g N k s ψ).coeff x = (levOfChar ψ hψ N true s k h).e x := by
  rw [eJ, coeff_eDat]
  unfold Lev.e
  congr 1
  · funext u
    unfold levOfChar Lev.Mem
    simp only [isUp_iff_isUniUp, forall_const]
    apply propext
    apply and_congr_right
    intro _
    constructor
    · intro H a b h1 h2 h3
      rw [show b = ⟨s + k, by omega⟩ from Fin.ext h3]
      have := H a h1 h2
      unfold entN at this
      rw [dif_pos ⟨a.isLt, by omega⟩] at this
      exact this
    · intro H a h1 h2
      unfold entN
      rw [dif_pos ⟨by omega, by omega⟩]
      exact H ⟨a, by omega⟩ ⟨s + k, by omega⟩ h1 h2 rfl
  · funext u
    have hE := sum_edge_eq_phiJ ψ hψ s k hN h (u : Matrix (Fin N) (Fin N) (ZMod g))
    unfold levOfChar at hE
    unfold levOfChar Lev.chi
    simp only [Units.val_one, one_mul]
    rw [hE]

end GlobalTheory.BadShare.Basic
