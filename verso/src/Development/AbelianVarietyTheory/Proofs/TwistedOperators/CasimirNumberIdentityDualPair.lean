import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.CasimirNumber

def sqSum (l : List ℚ) : ℚ := (l.map fun x => x ^ 2).sum

/- English proof (translation)
Unfold `sqSum`. Rewrite using `[List.map_append, List.sum_append]`.
-/
theorem sqSum_append (l₁ l₂ : List ℚ) : sqSum (l₁ ++ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold sqSum
  rw [List.map_append, List.sum_append]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [sqSum]`. Consider the case `cons a l ih`. Rewrite using `[List.length_cons, Finset.sum_range_succ']`. Simplify using `only [List.getD_cons_succ, List.getD_cons_zero]`.

Rewrite using `[ih]`. Unfold `sqSum`. Simplify using `only [List.map_cons, List.sum_cons]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_range_getD_sq (l : List ℚ) :
    ∑ i ∈ Finset.range l.length, (l.getD i 0) ^ 2 = sqSum l := by
  induction l with
  | nil => simp [sqSum]
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    unfold sqSum
    simp only [List.map_cons, List.sum_cons]
    ring

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (l.getD i 0) ^ 2)]`. Conclude with `sum_range_getD_sq l`.
-/
theorem sum_fin_getD_sq (l : List ℚ) (p : ℕ) (h : l.length = p) :
    ∑ i : Fin p, (l.getD i 0) ^ 2 = sqSum l := by
  subst h
  rw [Fin.sum_univ_eq_sum_range (fun i => (l.getD i 0) ^ 2)]
  exact sum_range_getD_sq l

/- English proof (translation)
Unfold `normSq ofBlocks`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only`. Rewrite using `[sum_fin_getD_sq l₁ p h₁, sum_fin_getD_sq l₂ q h₂]`.
-/
theorem normSq_ofBlocks {p q : ℕ} (l₁ l₂ : List ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    normSq (ofBlocks (p := p) (q := q) l₁ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold normSq ofBlocks
  rw [Fintype.sum_sum_type]
  simp only
  rw [sum_fin_getD_sq l₁ p h₁, sum_fin_getD_sq l₂ q h₂]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_range_sub_sq (c : ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (c - (i : ℚ)) ^ 2 =
      n * c ^ 2 - c * (n * (n - 1)) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/- English proof (translation)
Unfold `rhoSq`. Rewrite using `[sum_range_sub_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoSq_eq (n : ℕ) : rhoSq n = (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 12 := by
  unfold rhoSq
  rw [sum_range_sub_sq]
  ring

/- English proof (translation)
Unfold `Formalism.BasicNotions.TH.block`. Simplify using the standard rewrite rules.
-/
theorem length_block (t : ℕ) : (Formalism.BasicNotions.TH.block t).length = t := by
  unfold Formalism.BasicNotions.TH.block
  simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [sqSum]`. Consider the case `succ n ih`. Rewrite using `[List.range_succ, List.map_append, sqSum_append, ih, Finset.sum_range_succ]`. Simplify using `[sqSum]`.
-/
theorem sqSum_map_range (f : ℕ → ℚ) (n : ℕ) :
    sqSum ((List.range n).map f) = ∑ i ∈ Finset.range n, f i ^ 2 := by
  induction n with
  | zero => simp [sqSum]
  | succ n ih =>
    rw [List.range_succ, List.map_append, sqSum_append, ih, Finset.sum_range_succ]
    simp [sqSum]

/- English proof (translation)
Establish `hb : Formalism.BasicNotions.TH.block t = (List.range t).map (fun m : ℕ => ((t : ℚ) - 1) / 2 - m)`. Establish `hf : ∀ l : List ℕ, List.flatMap (fun a : ℕ => [(Nat.cast a : ℚ)]) l = List.map (fun a : ℕ => (Nat.cast a : ℚ)) l`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => rfl`.

Consider the case `cons a l ih => simp [List.flatMap_cons, ih]`. Unfold `Formalism.BasicNotions.TH.block`. Simplify using `only [List.bind_eq_flatMap, List.pure_def]`. Rewrite using `[hf, List.map_map]`. Both sides reduce to the same expression.

Rewrite using `[hb, sqSum_map_range]`. Unfold `rhoSq`. Both sides reduce to the same expression.
-/
theorem sqSum_block (t : ℕ) : sqSum (Formalism.BasicNotions.TH.block t) = rhoSq t := by
  have hb : Formalism.BasicNotions.TH.block t = (List.range t).map (fun m : ℕ => ((t : ℚ) - 1) / 2 - m) := by
    have hf : ∀ l : List ℕ, List.flatMap (fun a : ℕ => [(Nat.cast a : ℚ)]) l = List.map (fun a : ℕ => (Nat.cast a : ℚ)) l := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp [List.flatMap_cons, ih]
    unfold Formalism.BasicNotions.TH.block
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [hf, List.map_map]
    rfl
  rw [hb, sqSum_map_range]
  unfold rhoSq
  rfl

/- English proof (translation)
Unfold `lamA`. Rewrite using `[normSq_ofBlocks _ _ (by simp) (by simp), sqSum_append, sqSum_append]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_lamA (al be ga de : List ℚ) :
    normSq (lamA al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de := by
  unfold lamA
  rw [normSq_ofBlocks _ _ (by simp) (by simp), sqSum_append, sqSum_append]
  ring

/- English proof (translation)
Unfold `lamA'`. Apply the tactic sequence `rw [normSq_ofBlocks _ _ (by simp [length_block] <;> omega) (by simp <;> omega)]`. Simplify using `only [sqSum_append, sqSum_block]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_lamA' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamA' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamA'
  rw [normSq_ofBlocks _ _ (by simp [length_block] <;> omega) (by simp <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

/- English proof (translation)
Unfold `lamM'`. Apply the tactic sequence `rw [normSq_ofBlocks _ _ (by simp <;> omega) (by simp [length_block] <;> omega)]`. Simplify using `only [sqSum_append, sqSum_block]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_lamM' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamM' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamM'
  rw [normSq_ofBlocks _ _ (by simp <;> omega) (by simp [length_block] <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

/- English proof (translation)
Introduce `t al be ga de _`. Use `⟨?_, by rw [normSq_lamM', normSq_lamA']⟩` and prove the remaining obligations. Rewrite using `[normSq_lamA', normSq_lamA, rhoSq_eq, rhoSq_eq, rhoSq_eq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem casimir_number_identity : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → normSq (lamA' t al be ga de) - rhoSq (al.length + be.length + ga.length + de.length + t) = normSq (lamA al be ga de) - rhoSq (al.length + be.length + ga.length + de.length) - ((al.length + be.length + ga.length + de.length : ℕ) : ℚ) * ((al.length + be.length + ga.length + de.length + t : ℕ) : ℚ) * (t : ℚ) / 4 ∧ normSq (lamM' t al be ga de) = normSq (lamA' t al be ga de) := by
  intro t al be ga de _
  refine ⟨?_, by rw [normSq_lamM', normSq_lamA']⟩
  rw [normSq_lamA', normSq_lamA, rhoSq_eq, rhoSq_eq, rhoSq_eq]
  push_cast
  ring

end GlobalTheory.CasimirNumber
