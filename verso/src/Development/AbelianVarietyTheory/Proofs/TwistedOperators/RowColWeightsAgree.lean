import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowAddGenericRowAddTerm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ColumnDegreeLe

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.BlockWeights

def extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then a ⟨i, h⟩ else 0

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih]`. Distinguish the cases in `h : n < p`.

Establish `hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) = insert ⟨n, h⟩ (Finset.univ.filter (fun b : Fin p => (b : ℕ) < n))`. Use extensionality with `b`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, Finset.sum_insert (by simp), add_comm]`.

Simplify using `only [extZero, dif_pos h]`. Establish `hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) = Finset.univ.filter (fun b : Fin p => (b : ℕ) < n)`. Use extensionality with `b`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hset]`. Simplify using `only [extZero, dif_neg h, add_zero]`.
-/
theorem sum_range_extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a j =
      ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < p
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          insert ⟨n, h⟩ (Finset.univ.filter (fun b : Fin p => (b : ℕ) < n)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp), add_comm]
      simp only [extZero, dif_pos h]
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          Finset.univ.filter (fun b : Fin p => (b : ℕ) < n) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hset]
      simp only [extZero, dif_neg h, add_zero]

/- English proof (translation)
Establish `hinv : ∀ b c : Fin p, b < c → ∀ t : ℂ, bind₁ (fun s => X s + ∑ k, if s = z (c, k) then C t * X (z (b, k)) else 0) P = P`. Introduce `b c hbc t`. Establish `hw : Function.Injective (fun k : Fin r => z (c, k))` using `fun k l h => congrArg Prod.snd (hz h)`. Establish `huw : ∀ k l : Fin r, z (b, k) ≠ z (c, l)`. Introduce `k l h`.

Conclude with `(ne_of_lt hbc) (congrArg Prod.fst (hz h))`. Establish `hT` using `GlobalTheory.rowAdd_invariant_iff (K := ℂ) (fun k : Fin r => z (b, k)) (fun k : Fin r => z (c, k)) hw huw P`. Establish `h0 : ∑ k, X (z (b, k)) * pderiv (z (c, k)) P = 0`. Rewrite using `[← GlobalTheory.Capelli.rowOp_apply]`. Conclude with `hrow b c hbc`.

Establish `h12` using `hT.out 1 2`. Conclude with `h12.mpr h0 t`. Establish `hrowdeg : ∀ b, ∀ m ∈ P.support, ∑ k, m (z (b, k)) = a b`. Introduce `b m hm`. Conclude with `(GlobalTheory.JointHarm.rowOp_eq_smul_iff z b P _).mp (ha b) m hm` after adjusting the coercions.

Establish `hcoldeg : ∀ k, ∀ m ∈ P.support, ∑ b, m (z (b, k)) = a' k`. Introduce `k m hm`. Conclude with `(GlobalTheory.JointHarm.colOp_eq_smul_iff z k P _).mp (ha' k) m hm` after adjusting the coercions. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : P.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`.

Conclude with `hP`. Establish `key` using `GlobalTheory.column_degree_le z hz P a hrowdeg hinv (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)) m hm`. Establish `hcard : (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card ≤ i`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply] at hx`. Take `⟨k, hk, hkx⟩` from `hx`. Rewrite using `[Finset.mem_range, ← hkx]`. Conclude with `hk`.

Use `_ = i := Finset.card_range i`. Rewrite using `[sum_range_extZero, sum_range_extZero]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `b hb`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem partial_sum_le {σ : Type} [DecidableEq σ] {p r : ℕ} (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ)
    (hP : P ≠ 0) (hrow : ∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0)
    (ha : ∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) (ha' : ∀ i, colOp ℂ z i i P = (a' i : ℂ) • P)
    (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j := by

  have hinv : ∀ b c : Fin p, b < c → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ k, if s = z (c, k) then C t * X (z (b, k)) else 0) P = P := by
    intro b c hbc t
    have hw : Function.Injective (fun k : Fin r => z (c, k)) :=
      fun k l h => congrArg Prod.snd (hz h)
    have huw : ∀ k l : Fin r, z (b, k) ≠ z (c, l) := by
      intro k l h
      exact (ne_of_lt hbc) (congrArg Prod.fst (hz h))
    have hT := GlobalTheory.rowAdd_invariant_iff (K := ℂ) (fun k : Fin r => z (b, k))
      (fun k : Fin r => z (c, k)) hw huw P
    have h0 : ∑ k, X (z (b, k)) * pderiv (z (c, k)) P = 0 := by
      rw [← GlobalTheory.Capelli.rowOp_apply]
      exact hrow b c hbc
    have h12 := hT.out 1 2
    exact h12.mpr h0 t

  have hrowdeg : ∀ b, ∀ m ∈ P.support, ∑ k, m (z (b, k)) = a b := by
    intro b m hm
    exact_mod_cast (GlobalTheory.JointHarm.rowOp_eq_smul_iff z b P _).mp (ha b) m hm
  have hcoldeg : ∀ k, ∀ m ∈ P.support, ∑ b, m (z (b, k)) = a' k := by
    intro k m hm
    exact_mod_cast (GlobalTheory.JointHarm.colOp_eq_smul_iff z k P _).mp (ha' k) m hm
  obtain ⟨m, hm⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP
  have key := GlobalTheory.column_degree_le z hz P a hrowdeg hinv
    (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)) m hm
  have hcard : (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card ≤ i := by
    calc (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card
        = ((Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range i).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply] at hx
          obtain ⟨k, hk, hkx⟩ := hx
          rw [Finset.mem_range, ← hkx]
          exact hk
      _ = i := Finset.card_range i
  rw [sum_range_extZero, sum_range_extZero]
  calc ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), a' k
      = ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), ∑ b, m (z (b, k)) :=
        Finset.sum_congr rfl (fun k _ => (hcoldeg k m hm).symm)
    _ = ∑ b, ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), m (z (b, k)) :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p =>
          (b : ℕ) < (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card), a b := key
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
        apply Finset.sum_le_sum_of_subset
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        omega

/- English proof (translation)
Introduce `σ _ p r z hz P a a' hP hanti hrow hcol ha ha'`. Establish `h1 : ∀ i, ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j` using `partial_sum_le z hz P a a' hP hrow ha ha'`. Establish `h2 : ∀ i, ∑ j ∈ Finset.range i, extZero a j ≤ ∑ j ∈ Finset.range i, extZero a' j`. Establish `hz' : Function.Injective (fun w : Fin r × Fin p => z w.swap)` using `hz.comp Prod.swap_injective`. Establish `e : ∀ k l : Fin r, rowOp ℂ (fun w : Fin r × Fin p => z w.swap) k l = colOp ℂ z k l` using `fun k l => GlobalTheory.Capelli.rowOp_eq_colOp _ k l`.

Establish `e' : ∀ b c : Fin p, colOp ℂ (fun w : Fin r × Fin p => z w.swap) b c = rowOp ℂ z b c` using `fun b c => (GlobalTheory.Capelli.rowOp_eq_colOp z b c).symm`. Conclude with `partial_sum_le (fun w : Fin r × Fin p => z w.swap) hz' P a' a hP (fun k l hkl => by rw [e]; exact hcol k l hkl) (fun k => by rw [e]; exact ha' k) (fun b => by rw [e']; exact ha b)`. Establish `hsum : ∀ i, ∑ j ∈ Finset.range i, extZero a j = ∑ j ∈ Finset.range i, extZero a' j` using `fun i => le_antisymm (h2 i) (h1 i)`. Establish `heq : ∀ j, extZero a j = extZero a' j`. Introduce `j`.

Establish `hj` using `hsum (j + 1)`. Rewrite `hj` using `[Finset.sum_range_succ, Finset.sum_range_succ, hsum j]`. Use linear arithmetic over natural numbers and integers. Use `⟨extZero a, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Unfold `extZero`. Distinguish the cases in `hj : j < p`. Rewrite using `[dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]`. Conclude with `hanti (Fin.mk_le_mk.mpr hij)`. Rewrite using `[dif_neg hj]`.

Conclude with `Nat.zero_le _`. Introduce `i hi`. Distinguish the cases in `hp : p ≤ i`. Simplify using `[extZero, show ¬ i < p by omega]`. Rewrite using `[heq i]`.

Simplify using `[extZero, show ¬ i < r by omega]`. Introduce `i`. Simplify using `[extZero]`. Introduce `i`. Rewrite using `[heq]`.

Simplify using `[extZero]`.
-/
theorem row_col_weights_agree : ∀ (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ), Function.Injective z → ∀ (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ), P ≠ 0 → Antitone a → (∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0) → (∀ i j : Fin r, i < j → colOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i, colOp ℂ z i i P = (a' i : ℂ) • P) → ∃ α : ℕ → ℕ, Antitone α ∧ (∀ i, min p r ≤ i → α i = 0) ∧ (∀ i : Fin p, a i = α i) ∧ ∀ i : Fin r, a' i = α i := by
  intro σ _ p r z hz P a a' hP hanti hrow hcol ha ha'
  have h1 : ∀ i, ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j :=
    partial_sum_le z hz P a a' hP hrow ha ha'

  have h2 : ∀ i, ∑ j ∈ Finset.range i, extZero a j ≤ ∑ j ∈ Finset.range i, extZero a' j := by
    have hz' : Function.Injective (fun w : Fin r × Fin p => z w.swap) :=
      hz.comp Prod.swap_injective
    have e : ∀ k l : Fin r,
        rowOp ℂ (fun w : Fin r × Fin p => z w.swap) k l = colOp ℂ z k l :=
      fun k l => GlobalTheory.Capelli.rowOp_eq_colOp _ k l
    have e' : ∀ b c : Fin p,
        colOp ℂ (fun w : Fin r × Fin p => z w.swap) b c = rowOp ℂ z b c :=
      fun b c => (GlobalTheory.Capelli.rowOp_eq_colOp z b c).symm
    exact partial_sum_le (fun w : Fin r × Fin p => z w.swap) hz' P a' a hP
      (fun k l hkl => by rw [e]; exact hcol k l hkl) (fun k => by rw [e]; exact ha' k)
      (fun b => by rw [e']; exact ha b)
  have hsum : ∀ i, ∑ j ∈ Finset.range i, extZero a j = ∑ j ∈ Finset.range i, extZero a' j :=
    fun i => le_antisymm (h2 i) (h1 i)

  have heq : ∀ j, extZero a j = extZero a' j := by
    intro j
    have hj := hsum (j + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum j] at hj
    omega
  refine ⟨extZero a, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    unfold extZero
    by_cases hj : j < p
    · rw [dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
      exact hanti (Fin.mk_le_mk.mpr hij)
    · rw [dif_neg hj]
      exact Nat.zero_le _
  · intro i hi
    by_cases hp : p ≤ i
    · simp [extZero, show ¬ i < p by omega]
    · rw [heq i]
      simp [extZero, show ¬ i < r by omega]
  · intro i
    simp [extZero]
  · intro i
    rw [heq]
    simp [extZero]

end GlobalTheory.JointHarm.BlockWeights
