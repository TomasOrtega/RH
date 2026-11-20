import Mathlib

open Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticePoint

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `valuation k x ≤ γ at hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ hγ, fun y hy => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy`. Rewrite `hy` using `[Units.val_mk0]`. Use `show valuation k y ≤ γ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isOpen_valBall {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation k x ≤ γ at hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  change valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy
  rw [Units.val_mk0] at hy
  show valuation k y ≤ γ
  calc valuation k y = valuation k ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (y - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx

/- English proof (translation)
Introduce `k _ _ _ _ n x`. Set `γ : ValueGroupWithZero k` to `Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1`. Establish `hγ : γ ≠ 0` using `ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)`. Set `S : AddSubgroup k` to `{ carrier := {y | valuation k y ≤ γ} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `valuation k a ≤ γ at ha`.

Express the relevant statement in the definitionally equal form `valuation k b ≤ γ at hb`. Use `show valuation k (a + b) ≤ γ`. Conclude with `(Valuation.map_add _ _ _).trans (max_le ha hb)`. Use the proof step `zero_mem' := by show valuation k 0 ≤ γ`. Simplify using the standard rewrite rules.

Use the proof step `neg_mem' := fun {a} ha => by`. Express the relevant statement in the definitionally equal form `valuation k a ≤ γ at ha`. Use `show valuation k (-a) ≤ γ`. Rewrite using `[Valuation.map_neg] }` and apply the resulting hypothesis. Establish `hS : (S : Set k) = {y | valuation k y ≤ γ}` using `rfl`.

Use `⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.coe_pi, hS]`. Conclude with `isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ`. Rewrite using `[AddSubgroup.coe_pi, hS]`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ`.

Rewrite using `[AddSubgroup.mem_pi]`. Introduce `i _`. Use `show valuation k (x i) ≤ γ`. Conclude with `le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))`.
-/
theorem exists_compact_open_addSubgroup_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  intro k _ _ _ _ n x
  let γ : ValueGroupWithZero k := Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)
  let S : AddSubgroup k :=
    { carrier := {y | valuation k y ≤ γ}
      add_mem' := fun {a b} ha hb => by
        change valuation k a ≤ γ at ha
        change valuation k b ≤ γ at hb
        show valuation k (a + b) ≤ γ
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by
        show valuation k 0 ≤ γ
        simp
      neg_mem' := fun {a} ha => by
        change valuation k a ≤ γ at ha
        show valuation k (-a) ≤ γ
        rwa [Valuation.map_neg] }
  have hS : (S : Set k) = {y | valuation k y ≤ γ} := rfl
  refine ⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi, hS]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
  · rw [AddSubgroup.coe_pi, hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ
  · rw [AddSubgroup.mem_pi]
    intro i _
    show valuation k (x i) ≤ γ
    exact le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))

end GlobalTheory.CompanionTheory.LatticePoint
