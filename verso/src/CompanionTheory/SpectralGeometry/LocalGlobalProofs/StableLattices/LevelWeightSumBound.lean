import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

/- English proof (translation)
Establish `h : (A.filter fun i => i.1.1 = c).card ≤ (univ : Finset (Fin n)).card` using `Finset.card_le_card_of_injOn (fun i => i.1.2) (fun _ _ => mem_univ _) (by`. Introduce `x hx y hy hxy`. Establish `h1` using `(mem_filter.1 (mem_coe.1 hx)).2`. Establish `h2` using `(mem_filter.1 (mem_coe.1 hy)).2`. Conclude with `Subtype.ext (Prod.ext (h1.trans h2.symm) hxy))`.

Simplify using `using h`.
-/
theorem card_first_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.1 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.1 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.2) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) hxy))
  simpa using h

/- English proof (translation)
Establish `h : (A.filter fun i => i.1.2 = c).card ≤ (univ : Finset (Fin n)).card` using `Finset.card_le_card_of_injOn (fun i => i.1.1) (fun _ _ => mem_univ _) (by`. Introduce `x hx y hy hxy`. Establish `h1` using `(mem_filter.1 (mem_coe.1 hx)).2`. Establish `h2` using `(mem_filter.1 (mem_coe.1 hy)).2`. Conclude with `Subtype.ext (Prod.ext hxy (h1.trans h2.symm)))`.

Simplify using `using h`.
-/
theorem card_second_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.2 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.2 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.1) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext hxy (h1.trans h2.symm)))
  simpa using h

/- English proof (translation)
Establish `h1 : (((A.filter fun i => i.1.1 = c).card : ℕ) : ℝ) ≤ n`. Conclude with `card_first_le A c` after adjusting the coercions. Establish `h2 : (((A.filter fun i => i.1.2 = c).card : ℕ) : ℝ) ≤ n`. Conclude with `card_second_le A c` after adjusting the coercions. Establish `h3 : (0 : ℝ) ≤ ((A.filter fun i => i.1.1 = c).card : ℕ)` using `Nat.cast_nonneg _`.

Establish `h4 : (0 : ℝ) ≤ ((A.filter fun i => i.1.2 = c).card : ℕ)` using `Nat.cast_nonneg _`. Unfold `wt`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem abs_wt_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) : |wt A c| ≤ n := by
  have h1 : (((A.filter fun i => i.1.1 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_first_le A c
  have h2 : (((A.filter fun i => i.1.2 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_second_le A c
  have h3 : (0 : ℝ) ≤ ((A.filter fun i => i.1.1 = c).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((A.filter fun i => i.1.2 = c).card : ℕ) := Nat.cast_nonneg _
  unfold wt
  rw [abs_le]
  constructor <;> linarith

/- English proof (translation)
The claim follows from `|(2 : ℝ) * PI.UpqRep.rhoC ε a| ≤ n := by have h1 : (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n) have h2 : (((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by exact_mod_cast (card_ …`.
-/
theorem abs_two_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    |(2 : ℝ) * PI.UpqRep.rhoC ε a| ≤ n := by
  have h1 : (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h2 : (((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  unfold PI.UpqRep.rhoC
  rw [abs_le]
  constructor <;> linarith

/- English proof (translation)
The claim follows from `|modExp (fun j => Fin (d j)) i| ≤ (N : ℤ) := by have hN : ∑ j, (d j : ℤ) = N := by exact_mod_cast h have key : ∀ p : Fin M → Prop, ∀ [DecidablePred p], (0 : ℤ) ≤ ∑ b with p b, (d b : ℤ) ∧ ∑ b with p b, (d b : ℤ) ≤ N := fun p _ => ⟨sum_nonneg fun _ _ => Int.natCast_nonneg _, hN ▸ …`.
-/
theorem abs_modExp_le {M N : ℕ} (d : Fin M → ℕ) (h : ∑ j, d j = N) (i : Fin M) :
    |modExp (fun j => Fin (d j)) i| ≤ (N : ℤ) := by
  have hN : ∑ j, (d j : ℤ) = N := by exact_mod_cast h
  have key : ∀ p : Fin M → Prop, ∀ [DecidablePred p],
      (0 : ℤ) ≤ ∑ b with p b, (d b : ℤ) ∧ ∑ b with p b, (d b : ℤ) ≤ N := fun p _ =>
    ⟨sum_nonneg fun _ _ => Int.natCast_nonneg _, hN ▸ sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _⟩
  obtain ⟨a1, a2⟩ := key (fun b => i < b)
  obtain ⟨b1, b2⟩ := key (fun b => b < i)
  simp only [modExp, Fintype.card_fin]
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

namespace GlobalTheory.CompanionTheory.RgCOBlock

/- English proof (translation)
Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hsz : ((sz lev M i : ℕ) : ℝ) ≤ n`. Establish `: sz lev M i ≤ n` using `(card_le_univ _).trans_eq (Fintype.card_fin n)`. Conclude with `this` after adjusting the coercions. Establish `hsz0 : (0 : ℝ) ≤ ((sz lev M i : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Establish `hm : ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) ≤ n`. Conclude with `ClusterBound.abs_modExp_le (sz lev M) h i` after adjusting the coercions. Establish `hm0 : (0 : ℝ) ≤ ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ)`. Conclude with `abs_nonneg _` after adjusting the coercions. Establish `hterm : ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ‖((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ)`.

Introduce `a _`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Establish `h1` using `ClusterBound.abs_wt_le (omU ε lev) a`. Establish `h2` using `ClusterBound.abs_two_rhoC_le ε a`. Establish `h3` using `abs_sub (wt (omU ε lev) a) ((2 : ℝ) * PI.UpqRep.rhoC ε a)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤ ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ))`. Use `(norm_sum_le_of_le _ hterm).trans_eq ?_` and prove the remaining obligations. Rewrite using `[sum_const, nsmul_eq_mul]`. Both sides reduce to the same expression.

Establish `hmod : ‖(sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2)‖ = ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2)`. Rewrite using `[norm_mul, norm_div, Complex.norm_natCast, Complex.norm_intCast]`. Simplify using the standard rewrite rules. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hmod]`.

Establish `e1 : ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) ≤ (n : ℝ) * (2 * n)` using `mul_le_mul_of_nonneg_right hsz (by positivity)`. Establish `e2 : ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) ≤ (n : ℝ) * ((n : ℝ) / 2)` using `mul_le_mul hsz (by linarith) (by linarith) hn`. Use polynomial arithmetic with `[sq_nonneg (n : ℝ)]`.
-/
theorem norm_cluster_sum_le (n M : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Fin M) (h : ∑ j, sz lev M j = n) :
    ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ) -
      ((sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2))‖ ≤ 3 * (n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsz : ((sz lev M i : ℕ) : ℝ) ≤ n := by
    have : sz lev M i ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast this
  have hsz0 : (0 : ℝ) ≤ ((sz lev M i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) ≤ n := by
    exact_mod_cast ClusterBound.abs_modExp_le (sz lev M) h i
  have hm0 : (0 : ℝ) ≤ ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) := by
    exact_mod_cast abs_nonneg _
  have hterm : ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ‖((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) := by
    intro a _
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := ClusterBound.abs_wt_le (omU ε lev) a
    have h2 := ClusterBound.abs_two_rhoC_le ε a
    have h3 := abs_sub (wt (omU ε lev) a) ((2 : ℝ) * PI.UpqRep.rhoC ε a)
    linarith
  have hsum : ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤
      ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) := by
    refine (norm_sum_le_of_le _ hterm).trans_eq ?_
    rw [sum_const, nsmul_eq_mul]
    rfl
  have hmod : ‖(sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2)‖ =
      ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_intCast]
    simp
  refine (norm_sub_le _ _).trans ?_
  rw [hmod]
  have e1 : ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) ≤ (n : ℝ) * (2 * n) :=
    mul_le_mul_of_nonneg_right hsz (by positivity)
  have e2 : ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) ≤
      (n : ℝ) * ((n : ℝ) / 2) :=
    mul_le_mul hsz (by linarith) (by linarith) hn
  nlinarith [sq_nonneg (n : ℝ)]

end GlobalTheory.CompanionTheory.RgCOBlock
