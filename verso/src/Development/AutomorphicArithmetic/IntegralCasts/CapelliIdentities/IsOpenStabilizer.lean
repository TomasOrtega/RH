import Mathlib

/- English proof (translation)
Introduce `G _ _ _ V _ _ ρ v h`. Set `H : Subgroup G` to `{ carrier := {g : G | ρ g v = v} one_mem' := by simp mul_mem' := by`. Introduce `a b ha hb`. Establish `ha' : ρ a v = v` using `ha`. Establish `hb' : ρ b v = v` using `hb`.

Express the relevant statement in the definitionally equal form `ρ (a * b) v = v`. Rewrite using `[map_mul, Module.End.mul_apply, hb', ha']`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Establish `ha' : ρ a v = v` using `ha`.

Express the relevant statement in the definitionally equal form `ρ a⁻¹ v = v`. Combine the equalities or inequalities in the displayed calculation. Conclude with `H.isOpen_of_mem_nhds (g := 1) h`.
-/
theorem UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G _ _ _ V _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {g : G | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        change ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by simp }
  exact H.isOpen_of_mem_nhds (g := 1) h
