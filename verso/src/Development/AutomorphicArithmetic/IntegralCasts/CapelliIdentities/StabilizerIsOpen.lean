import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open.{u_1, u_2} :
    ∀ {G : Type u_1} {V : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
    {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} ∈ nhds (1 : G) →
      IsOpen {k : G | ((ρ : G → V →ₗ[ℂ] V) k : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {k : G | ρ k v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h1 }
  exact H.isOpen_of_mem_nhds h
