import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds

open GlobalTheory

namespace GlobalTheory
namespace ShufflePositions

variable {A : Type} [DecidableEq A]

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl]`. Conclude with `Multiset.count_map_eq_count' (List.cons a) s List.cons_injective x`. Rewrite using `[if_neg hab, Multiset.count_eq_zero]`.

Introduce `hmem`. Take `⟨y, -, hy⟩` from `Multiset.mem_map.1 hmem`. Conclude with `hab (List.cons.inj hy).1.symm`.
-/
theorem count_cons_map (a b : A) (x : List A) (s : Multiset (List A)) :
    (s.map (List.cons b)).count (a :: x) = if a = b then s.count x else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    exact Multiset.count_map_eq_count' (List.cons a) s List.cons_injective x
  · rw [if_neg hab, Multiset.count_eq_zero]
    intro hmem
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
    exact hab (List.cons.inj hy).1.symm

omit [DecidableEq A] in
/- English proof (translation)
Rewrite using `[List.finRange_succ, List.filter_cons, List.filter_map]`. Consider the cases of `h0 : p 0`. Simplify using `[List.map_map, Function.comp_def]`. Simplify using `[List.map_map, Function.comp_def]`.
-/
theorem pos_cons {n : ℕ} (w : Fin (n + 1) → A) (p : Fin (n + 1) → Bool) :
    ((List.finRange (n + 1)).filter p).map w =
      (if p 0 then [w 0] else []) ++
        ((List.finRange n).filter fun j => p j.succ).map (fun j => w j.succ) := by
  rw [List.finRange_succ, List.filter_cons, List.filter_map]
  cases h0 : p 0
  · simp [List.map_map, Function.comp_def]
  · simp [List.map_map, Function.comp_def]

/- English proof (translation)
Rewrite using `[← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]`. Both sides reduce to the same expression.
-/
private theorem sum_filter_sub_sum_filter_and_not_eq_sum {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → Bool) → M) :
    ∑ ε, f ε = ∑ ε : Fin n → Bool, (f (Fin.cons true ε) + f (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl

/- English proof (translation)
Rewrite using `[← Multiset.map_singleton (List.cons a) u]`. Conclude with `count_cons_map c a x {u}`.
-/
private theorem count_cons_singleton_cons (c a : A) (x u : List A) :
    ({a :: u} : Multiset (List A)).count (c :: x) =
      if c = a then ({u} : Multiset (List A)).count x else 0 := by
  rw [← Multiset.map_singleton (List.cons a) u]
  exact count_cons_map c a x {u}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem count_cons_singleton_nil (c : A) (x : List A) :
    ({[]} : Multiset (List A)).count (c :: x) = 0 := by
  simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `w u v`. Simplify using `only [List.ofFn_zero, List.finRange_zero, List.filter_nil, List.map_nil, Finset.univ_unique, Finset.sum_singleton]`. Apply the tactic sequence `rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `[Shuffle.shuffle_nil_right]`. Rewrite using `[Shuffle.shuffle_cons_cons]`. Simplify using `[Multiset.mem_map]`.

Consider the case `succ n ih`. Introduce `w u v`. Rewrite using `[sum_filter_sub_sum_filter_and_not_eq_sum, List.ofFn_succ]`. Simplify using `only [pos_cons, Fin.cons_zero, Fin.cons_succ, Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false, List.nil_append, List.singleton_append]`. Use `set w' : Fin n → A := fun j => w j.succ with hw'`.

Apply the tactic sequence `rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩`. Simplify using the standard rewrite rules. Establish `h` using `ih w' [] v`. Rewrite `h` using `[Shuffle.shuffle_nil_left]`. Rewrite using `[Shuffle.shuffle_nil_left, count_cons_singleton_cons]`.

Simplify using `only [count_cons_singleton_cons, count_cons_singleton_nil, zero_mul, add_zero]`. Distinguish the cases in `hc : w 0 = b`. Simplify using `only [if_pos hc, h]`. Simplify using `[if_neg hc]`. Establish `h` using `ih w' u []`.

Rewrite `h` using `[Shuffle.shuffle_nil_right]`. Rewrite using `[Shuffle.shuffle_nil_right, count_cons_singleton_cons]`. Simplify using `only [count_cons_singleton_cons, count_cons_singleton_nil, mul_zero, zero_add]`. Distinguish the cases in `hc : w 0 = a`. Simplify using `only [if_pos hc, h]`.

Simplify using `[if_neg hc]`. Establish `h1` using `ih w' u (b :: v)`. Establish `h2` using `ih w' (a :: u) v`. Rewrite using `[Shuffle.shuffle_cons_cons, Multiset.count_add, count_cons_map, count_cons_map]`. Simplify using `only [count_cons_singleton_cons, Finset.sum_add_distrib]`.

Rewrite using `[add_comm]`. Use `congr 1`. Distinguish the cases in `hc : w 0 = b`. Simplify using `only [if_pos hc, h2]`. Simplify using `[if_neg hc]`.

Distinguish the cases in `hc : w 0 = a`. Simplify using `only [if_pos hc, h1]`. Simplify using `[if_neg hc]`.
-/
theorem count_single (n : ℕ) : ∀ (w : Fin n → A) (u v : List A),
    (Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool,
        ({u} : Multiset (List A)).count (((List.finRange n).filter fun j => !ε j).map w) *
        ({v} : Multiset (List A)).count (((List.finRange n).filter ε).map w) := by
  induction n with
  | zero =>
    intro w u v
    simp only [List.ofFn_zero, List.finRange_zero, List.filter_nil, List.map_nil,
      Finset.univ_unique, Finset.sum_singleton]
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · simp
    · simp [Shuffle.shuffle_nil_right]
    · rw [Shuffle.shuffle_cons_cons]
      simp [Multiset.mem_map]
  | succ n ih =>
    intro w u v
    rw [sum_filter_sub_sum_filter_and_not_eq_sum, List.ofFn_succ]
    simp only [pos_cons, Fin.cons_zero, Fin.cons_succ, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, List.nil_append, List.singleton_append]
    set w' : Fin n → A := fun j => w j.succ with hw'
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · have h := ih w' [] v
      rw [Shuffle.shuffle_nil_left] at h
      rw [Shuffle.shuffle_nil_left, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, zero_mul, add_zero]
      by_cases hc : w 0 = b
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h := ih w' u []
      rw [Shuffle.shuffle_nil_right] at h
      rw [Shuffle.shuffle_nil_right, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, mul_zero, zero_add]
      by_cases hc : w 0 = a
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h1 := ih w' u (b :: v)
      have h2 := ih w' (a :: u) v
      rw [Shuffle.shuffle_cons_cons, Multiset.count_add, count_cons_map, count_cons_map]
      simp only [count_cons_singleton_cons, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · by_cases hc : w 0 = b
        · simp only [if_pos hc, h2]
        · simp [if_neg hc]
      · by_cases hc : w 0 = a
        · simp only [if_pos hc, h1]
        · simp [if_neg hc]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons, Multiset.count_singleton, add_comm]`.
-/
private theorem sum_map_count_singleton (X : List A) (s : Multiset (List A)) :
    (s.map fun v => ({v} : Multiset (List A)).count X).sum = s.count X := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons, Multiset.count_singleton,
      add_comm]

/- English proof (translation)
Simplify using `only [Multiset.count_bind, count_single n w, Multiset.sum_map_sum]`. Use `Finset.sum_congr rfl fun ε _ => ?_` and prove the remaining obligations. Simplify using `only [Multiset.sum_map_mul_left, Multiset.sum_map_mul_right, sum_map_count_singleton]`.
-/
theorem count_bind_shuffle (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A)
    (s₁ s₂ : Multiset (List A)) :
    (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) *
        s₂.count (((List.finRange n).filter ε).map w) := by
  simp only [Multiset.count_bind, count_single n w, Multiset.sum_map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [Multiset.sum_map_mul_left, Multiset.sum_map_mul_right, sum_map_count_singleton]

end ShufflePositions
end GlobalTheory
