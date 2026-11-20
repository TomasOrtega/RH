import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.UnipCompact

variable {n : Type}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩`.
-/
theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `e : (unipOf k c : Set (GL n k)) = ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_setOf_eq]`. Rewrite using `[e]`.

Use `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const`.
-/
theorem isClosed_unipOf (c : n → ℤ) : IsClosed (unipOf k c : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (unipOf k c : Set (GL n k)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

/- English proof (translation)
Establish `key : ∀ u ∈ unipOf k c, ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j)`. Introduce `u hu`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Distinguish the cases in `h : c i < c j`.

Use `filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm`. Use `hm.mono ?_` and prove the remaining obligations. Use polynomial arithmetic with `[Int.natCast_nonneg m]`. Rewrite using `[mem_unipOf.1 hu i j h]`. Use `Filter.Eventually.of_forall fun m => ?_` and prove the remaining obligations.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[GlobalTheory.IwahoriInj.deep_zero_iff]`. Simplify using `[one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]`. Conclude with `(key u hu).and (key _ (inv_mem hu))`.
-/
theorem eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by
  have key : ∀ u ∈ unipOf k c, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    by_cases h : c i < c j
    · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      nlinarith [Int.natCast_nonneg m]
    · rw [mem_unipOf.1 hu i j h]
      refine Filter.Eventually.of_forall fun m => ?_
      by_cases hij : i = j
      · subst hij
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

/- English proof (translation)
Take `⟨m, hm⟩` from `((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists`. Use `⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ unipOf k c, inf_le_right, ?_, fun u hu => ⟨hm u hu, hS u hu⟩⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_inf]`. Conclude with `(GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (isClosed_unipOf c)`.
-/
theorem exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (isClosed_unipOf c)

end GlobalTheory.UnipCompact
