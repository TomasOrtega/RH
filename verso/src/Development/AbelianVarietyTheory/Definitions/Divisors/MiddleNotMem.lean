import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

def twoPhase (x : Matrix (n ⊕ Fin 2) (n' ⊕ Fin 3) k) (x' : Matrix (n'' ⊕ Fin 1) (n ⊕ Fin 2) k) : k :=
  ch x + ch x' + ∑ r, x' (.inr 0) (.inl r) * x (.inl r) (.inr 1)

/- English proof (translation)
Simplify using `[twoPhase, ch, colE, upU, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, stepPt, basePt, Free, Kept, one_apply, mul_add, Finset.sum_add_distrib]`. Rewrite using `[Finset.filter_singleton, if_neg (Fin.succ_ne_zero _).symm]`. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twoPhase_upU (x₀ : Matrix n n' k) (e : StepVar n 2 n' → k) (x' : Matrix (n'' ⊕ Fin 1) (n ⊕ Fin 2) k)
    (β : n → k) : twoPhase ((colE 2 2 β).val * stepPt x₀ e) (x' * (colE 2 2 (-β)).val) = twoPhase (stepPt x₀ e) x' := by
  simp [twoPhase, ch, colE, upU, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, stepPt, basePt, Free, Kept,
    one_apply, mul_add, Finset.sum_add_distrib]
  rw [Finset.filter_singleton, if_neg (Fin.succ_ne_zero _).symm]
  simp only [Finset.card_empty, Nat.cast_zero]
  ring

/- English proof (translation)
Simplify using `[twoPhase, ch, rowE, lowU, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, stepPt, basePt, Free, Kept, one_apply, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twoPhase_lowU (x : Matrix (n ⊕ Fin 2) (n' ⊕ Fin 3) k) (x₀ : Matrix n'' n k) (e : StepVar n'' 1 n → k)
    (u : n → k) : twoPhase ((rowE 2 1 u).val * x) (stepPt x₀ e * (rowE 2 1 (-u)).val) = twoPhase x (stepPt x₀ e) := by
  simp [twoPhase, ch, rowE, lowU, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, stepPt, basePt, Free, Kept,
    one_apply, add_mul, Finset.sum_add_distrib]
  ring

/- English proof (translation)
Rewrite using `[symN_even]`. Conclude with `⟨Subgroup.mem_sup_right (RootEx.Model.rowE_mem ρ u), Subgroup.mem_sup_left (RootEx.Model.colE_mem ρ β)⟩`.
-/
theorem heis_mem (ρ : ℕ) (u β : n → k) : rowE (2 * ρ) ρ u ∈ symN k n (2 * ρ) ∧ colE (2 * ρ) (ρ + 1) β ∈ symN k n (2 * ρ) := by
  rw [symN_even]
  exact ⟨Subgroup.mem_sup_right (RootEx.Model.rowE_mem ρ u), Subgroup.mem_sup_left (RootEx.Model.colE_mem ρ β)⟩

/- English proof (translation)
Rewrite using `[symN_odd]`. Conclude with `RootEx.Model.rowE_not_mem (c := 2 * ρ + 1) ⟨ρ, by omega⟩ u hu`.
-/
theorem middle_not_mem (ρ : ℕ) (u : n → k) (hu : u ≠ 0) : rowE (2 * ρ + 1) (ρ + 1) u ∉ symN k n (2 * ρ + 1) := by
  rw [symN_odd]
  exact RootEx.Model.rowE_not_mem (c := 2 * ρ + 1) ⟨ρ, by omega⟩ u hu

/- English proof (translation)
Establish `h : ∀ p, N k n 0 p = ⊥` using `fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by`. Use extensionality with `(r | r) (s | s)`. Conclude with `RootEx.Model.mem_N_iff.1 hg _ _ le_rfl`. Apply the tactic sequence `all_goals first | exact r.elim0 | exact s.elim0)`. Use extensionality with `g`.

Use `show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _`. Simplify using `[symN, h]`.
-/
theorem symPr_zero (C : Subgroup (GL (n ⊕ Fin 0) k)) : symPr C = C.comap (embX 0) := by
  have h : ∀ p, N k n 0 p = ⊥ := fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by
    ext (r | r) (s | s)
    · exact RootEx.Model.mem_N_iff.1 hg _ _ le_rfl
    all_goals first | exact r.elim0 | exact s.elim0)
  ext g
  show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _
  simp [symN, h]
end Alg

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

/- English proof (translation)
Use function extensionality and compare the values at `X`. Take `⟨i, j⟩` from `X`. Distinguish the cases in `hi : i = G.m`. Substitute `hi` using the available equality. Rewrite using `[Reps.elt, onColumn_apply]`.

Consider the cases of `j with`. Consider the case `zero => rfl`. Consider the case `succ j => simp [Reps.through]`. Simplify using `[Reps.elt, onColumn, hi]`.
-/
theorem elt_one (J : G.Level) :
    (Reps.through hs J fun _ => 1).elt (fun _ => DoubleCoset.mk _ _ 1) = 1 := by
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    rw [Reps.elt, onColumn_apply]
    cases j with
    | zero => rfl
    | succ j => simp [Reps.through]
  · simp [Reps.elt, onColumn, hi]

omit [MeasurableSpace k] [BorelSpace k] in

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `: charFactor G 1 = 1` using `by simp [charFactor]`. Apply the tactic sequence `cases keep <;> simp [moved, Grid.pathAct_one, this]`.
-/
theorem moved_one (keep : Bool) (T : G.Args → ℂ) : moved G keep 1 T = T := by
  funext z
  have : charFactor G 1 = 1 := by simp [charFactor]
  cases keep <;> simp [moved, Grid.pathAct_one, this]

/- English proof (translation)
Establish `h : (unfTerm ψ ν keep (Reps.through hs J fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).datum 0 0 = 1`. Simplify using `only [unfTerm, elt_one, moved_one]`. Conclude with `(flatTensor_vacuum hs ψ ν hψ hν S h1 h0).2`. Use `⟨h, fun H => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[H]`.

Conclude with `zero_ne_one h`.
-/
theorem vacuum_term (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) (J : G.Level) (keep : Bool) :
    (unfTerm ψ ν keep (Reps.through hs J fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).datum 0 0 = 1 ∧
    (fun _ => DoubleCoset.mk _ _ 1) ∈ unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S := by
  have h : (unfTerm ψ ν keep (Reps.through hs J fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).datum 0 0 = 1 := by
    simp only [unfTerm, elt_one, moved_one]
    exact (flatTensor_vacuum hs ψ ν hψ hν S h1 h0).2
  refine ⟨h, fun H => ?_⟩
  rw [H] at h
  exact zero_ne_one h

/- English proof (translation)
Establish `: IsEmpty (Fin (G.m - 2))` using `by rw [hm]; exact Fin.isEmpty'`. Take `⟨a, b⟩` from `vacuum_term hs ψ ν hψ hν S h1 h0 J keep`. Establish `hS : unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S = {fun _ => DoubleCoset.mk _ _ 1}` using `Set.eq_singleton_iff_unique_mem.2 ⟨b, fun β _ => funext fun i => isEmptyElim i⟩`. Use `⟨hS ▸ Set.finite_singleton _, _, ?_, ?_, a⟩` and prove the remaining obligations. Simplify using `[unf, hS]`.

Simplify using `[unfTerm]`.
-/
theorem unf_two (hm : G.m = 2) (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) (J : G.Level) (keep : Bool) :
    ∃ (hfin : (unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S).Finite) (t : UnfTerm G),
      unf ψ ν keep _ S hfin = {t} ∧ t.coef = 1 ∧ t.datum 0 0 = 1 := by
  have : IsEmpty (Fin (G.m - 2)) := by rw [hm]; exact Fin.isEmpty'
  obtain ⟨a, b⟩ := vacuum_term hs ψ ν hψ hν S h1 h0 J keep
  have hS : unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S = {fun _ => DoubleCoset.mk _ _ 1} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨b, fun β _ => funext fun i => isEmptyElim i⟩
  refine ⟨hS ▸ Set.finite_singleton _, _, ?_, ?_, a⟩
  · simp [unf, hS]
  · simp [unfTerm]

end GlobalTheory.FunObj.UnfModel
