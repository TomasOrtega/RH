import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace InfiniteFiniteFactorization

open Classical

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _`. Conclude with `h`. Consider the case `succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))`.
-/
theorem stepInf (h6 : G6) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (m : Pl E → ℕ)
    (h : St ψ S Y Y' 0 m) : ∀ n, n ≤ a - 1 → St ψ S Y Y' n m := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Rewrite using `[Function.update_eq_self_iff.mpr hm.symm]`. Conclude with `h`.

Consider the case `succ k ih`. Introduce `hk`. Establish `h'` using `h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw (by simp only [Function.update_self]; omega) (ih (by omega))`. Simplify `h'` using `only [Function.update_self, Function.update_idem]`.
-/
theorem stepFin (h7 : G7) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (w : Pl E) (hw : w ∈ S)
    (n : ℕ) (m : Pl E → ℕ) (hm : m w = 0) (h : St ψ S Y Y' n m) :
    ∀ k, k ≤ a - 1 → St ψ S Y Y' n (Function.update m w k) := by
  intro k
  induction k with
  | zero => intro _; rw [Function.update_eq_self_iff.mpr hm.symm]; exact h
  | succ k ih =>
    intro hk
    have h' := h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw
      (by simp only [Function.update_self]; omega) (ih (by omega))
    simpa only [Function.update_self, Function.update_idem] using h'

end InfiniteFiniteFactorization

open InfiniteFiniteFactorization in
/- English proof (translation)
Introduce `h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0`. Establish `h1` using `stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl`. Establish `key : ∀ T : Finset (Pl E), T ⊆ S → St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0)`. Introduce `T`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations.

Introduce `_`. Simplify using `using h1`. Introduce `x T hx ih hT`. Establish `h` using `stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1) (fun w => if w ∈ T then a - 1 else 0) (by simp [hx]) (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = x`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hw]`.

Conclude with `key S subset_rfl`.
-/
theorem whittaker_factorization_places : G6 → G7 → FourierInductionSteps := by
  classical
  intro h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0
  have h1 := stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl
  have key : ∀ T : Finset (Pl E), T ⊆ S →
      St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      simpa using h1
    · intro x T hx ih hT
      have h := stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1)
        (fun w => if w ∈ T then a - 1 else 0) (by simp [hx])
        (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl
      convert h using 1
      funext w
      by_cases hw : w = x
      · subst hw; simp
      · simp [hw]
  exact key S subset_rfl

end PositivityTheory.jumpWindows

end
