import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

/- English proof (translation)
Use `set T : ℕ → ℝ := fun i => num (fun k : Fin (e + 1) => if (k : ℕ) < i then x + d else x) with hT`. Establish `h1 : num (fun _ => x + d) = T (e + 1)`. Simplify using `only [hT]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[if_pos k.2]`. Establish `h0 : num (fun _ => x) = T 0`. Simplify using `[hT]`. Rewrite using `[h1, h0, ← Finset.sum_range_sub]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi' : i < e + 1` using `Finset.mem_range.1 hi`. Establish `ha : T (i + 1) = num (Fin.cons (x + d) (fun l : Fin e => if (l : ℕ) < i then x + d else x))`. Simplify using `only [hT]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Use `Fin.cases ?_ (fun l => ?_) k` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `hf : (Fin.cons x (fun l : Fin e => if (l : ℕ) < i then x + d else x) : Fin (e + 1) → V) = fun k : Fin (e + 1) => if 0 < (k : ℕ) ∧ (k : ℕ) ≤ i then x + d else x`. Use function extensionality and compare the values at `k`.

Use `Fin.cases ?_ (fun l => ?_) k` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[Nat.succ_le_iff]`. Establish `hb : T i = num (Fin.cons x (fun l : Fin e => if (l : ℕ) < i then x + d else x))`. Rewrite using `[hf, ← hs _ (Equiv.swap 0 ⟨i, hi'⟩)]`.

Simplify using `only [hT]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations.

Establish `hk0 : k = 0 ↔ (k : ℕ) = 0` using `Fin.ext_iff`. Establish `hki : k = ⟨i, hi'⟩ ↔ (k : ℕ) = i` using `Fin.ext_iff`. Rewrite using `[Equiv.swap_apply_def]`. Distinguish the cases in `c0 : k = 0`. Rewrite using `[if_pos c0]`.

Use `hk0.1 c0` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg c0]`. Distinguish the cases in `ci : k = ⟨i, hi'⟩`.

Rewrite using `[if_pos ci]`. Use `hki.1 ci` as an intermediate fact. Simplify using `only [Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg ci]`.

Establish `h2` using `mt hk0.2 c0`. Establish `h3` using `mt hki.2 ci`. Use linear arithmetic over natural numbers and integers. Rewrite using `[ha, hb, MultilinearMap.cons_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symm_multilinear_telescope {e : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]
    (num : MultilinearMap ℝ (fun _ : Fin (e + 1) => V) ℝ)
    (hs : ∀ (v : Fin (e + 1) → V) (π : Equiv.Perm (Fin (e + 1))), num (v ∘ π) = num v) (x d : V) :
    num (fun _ => x + d) - num (fun _ => x) =
      ∑ i ∈ Finset.range (e + 1), num (Fin.cons d (fun l : Fin e => if (l : ℕ) < i then x + d else x)) := by
  set T : ℕ → ℝ := fun i => num (fun k : Fin (e + 1) => if (k : ℕ) < i then x + d else x) with hT
  have h1 : num (fun _ => x + d) = T (e + 1) := by
    simp only [hT]
    congr 1
    funext k
    rw [if_pos k.2]
  have h0 : num (fun _ => x) = T 0 := by
    simp [hT]
  rw [h1, h0, ← Finset.sum_range_sub]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < e + 1 := Finset.mem_range.1 hi
  have ha : T (i + 1) = num (Fin.cons (x + d) (fun l : Fin e => if (l : ℕ) < i then x + d else x)) := by
    simp only [hT]
    congr 1
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp
    · simp
  have hf : (Fin.cons x (fun l : Fin e => if (l : ℕ) < i then x + d else x) : Fin (e + 1) → V) =
      fun k : Fin (e + 1) => if 0 < (k : ℕ) ∧ (k : ℕ) ≤ i then x + d else x := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp
    · simp [Nat.succ_le_iff]
  have hb : T i = num (Fin.cons x (fun l : Fin e => if (l : ℕ) < i then x + d else x)) := by
    rw [hf, ← hs _ (Equiv.swap 0 ⟨i, hi'⟩)]
    simp only [hT]
    congr 1
    funext k
    simp only [Function.comp]
    refine if_congr ?_ rfl rfl
    have hk0 : k = 0 ↔ (k : ℕ) = 0 := Fin.ext_iff
    have hki : k = ⟨i, hi'⟩ ↔ (k : ℕ) = i := Fin.ext_iff
    rw [Equiv.swap_apply_def]
    by_cases c0 : k = 0
    · rw [if_pos c0]
      have := hk0.1 c0
      simp only
      omega
    · rw [if_neg c0]
      by_cases ci : k = ⟨i, hi'⟩
      · rw [if_pos ci]
        have := hki.1 ci
        simp only [Fin.val_zero]
        omega
      · rw [if_neg ci]
        have h2 := mt hk0.2 c0
        have h3 := mt hki.2 ci
        omega
  rw [ha, hb, MultilinearMap.cons_add]
  ring

/- English proof (translation)
Introduce `e M K v u hu`. Unfold `Calc.top`. Rewrite using `[symm_multilinear_telescope K.num K.symm v (K.ar u)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[K.num_ar u hu]`.

Use `congr 1`. Use function extensionality and compare the values at `l`. Conclude with `apply_ite _ _ _ _`.
-/
theorem top_add_ar_sub : ∀ (e : ℕ) (M : Man e) (K : Calc M) (v : K.V) (u : M.Fun), M.Smooth u →
    K.top (v + K.ar u) - K.top v = ∑ i ∈ Finset.range (e + 1),
      M.int (fun l : Fin e => if (l : ℕ) < i then K.c1 (v + K.ar u) else K.c1 v) u := by
  intro e M K v u hu
  unfold Calc.top
  rw [symm_multilinear_telescope K.num K.symm v (K.ar u)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [K.num_ar u hu]
  congr 1
  funext l
  exact apply_ite _ _ _ _

end GlobalTheory.Mean4O
