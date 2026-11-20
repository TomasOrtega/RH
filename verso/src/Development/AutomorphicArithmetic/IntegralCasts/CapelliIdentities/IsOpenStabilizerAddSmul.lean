import Mathlib

/- English proof (translation)
Introduce `G V _ _ _ _ _ ρ a b z ha hb`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g hg`. Establish `hg' : ρ g (a + z • b) = a + z • b` using `hg`. Establish `hc : Continuous fun x : G => g⁻¹ * x` using `continuous_const.mul continuous_id`.

Establish `hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' ({g : G | ρ g a = a} ∩ {g : G | ρ g b = b}))` using `(ha.inter hb).preimage hc`. Use `Filter.mem_of_superset (hU.mem_nhds ?_) ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `x hx`. Establish `h1 : ρ (g⁻¹ * x) a = a` using `hx.1`.

Establish `h2 : ρ (g⁻¹ * x) b = b` using `hx.2`. Establish `h3 : ρ (g⁻¹ * x) (a + z • b) = a + z • b`. Rewrite using `[map_add, map_smul, h1, h2]`. Establish `h4 : x = g * (g⁻¹ * x)` using `by group`. Use `show ρ x (a + z • b) = a + z • b`.

Rewrite using `[h4, map_mul, Module.End.mul_apply, h3, hg']`.
-/
theorem UpperTheory.isOpen_stabilizer_add_smul :
    ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) (a b : V) (z : ℂ),
        IsOpen {g : G | ρ g a = a} → IsOpen {g : G | ρ g b = b} → IsOpen {g : G | ρ g (a + z • b) = a + z • b} := by
  intro G V _ _ _ _ _ ρ a b z ha hb
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hg' : ρ g (a + z • b) = a + z • b := hg
  have hc : Continuous fun x : G => g⁻¹ * x := continuous_const.mul continuous_id
  have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' ({g : G | ρ g a = a} ∩ {g : G | ρ g b = b})) :=
    (ha.inter hb).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · simp
  · intro x hx
    have h1 : ρ (g⁻¹ * x) a = a := hx.1
    have h2 : ρ (g⁻¹ * x) b = b := hx.2
    have h3 : ρ (g⁻¹ * x) (a + z • b) = a + z • b := by
      rw [map_add, map_smul, h1, h2]
    have h4 : x = g * (g⁻¹ * x) := by group
    show ρ x (a + z • b) = a + z • b
    rw [h4, map_mul, Module.End.mul_apply, h3, hg']
