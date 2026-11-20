import Mathlib

noncomputable def UpperTheory.Reformulated.B.CyclicSubtraction.cycSub.{u_1, u_2} :
    {G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : AddCommGroup M] → Representation ℤ G M → G → M →+ M :=
    fun {G : Type u_1} {M : Type u_2} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) (σ : G) ↦
      ((ρ : G → M →ₗ[ℤ] M) σ - LinearMap.id).toAddMonoidHom

/- English proof (translation)
Introduce `G M _ _ ρ σ hσ x hx g`. Establish `h0 : ρ σ x - x = 0` using `hx`. Establish `h1 : ρ σ x = x` using `sub_eq_zero.mp h0`. Set `H : Subgroup G` to `{ carrier := {g | ρ g x = x} one_mem' := by show ρ 1 x = x`. Rewrite using `[map_one]`.

Both sides reduce to the same expression. Use the proof step `mul_mem' := by`. Introduce `a b ha hb`. Establish `ha' : ρ a x = x` using `ha`. Establish `hb' : ρ b x = x` using `hb`.

Use `show ρ (a * b) x = x`. Rewrite using `[map_mul, Module.End.mul_apply, hb', ha']`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Establish `ha' : ρ a x = x` using `ha`.

Use `show ρ a⁻¹ x = x`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel, map_one]`. Use `rfl }`. Establish `hle : Subgroup.zpowers σ ≤ H` using `(Subgroup.zpowers_le).mpr h1`.

Conclude with `hle (hσ g)`.
-/
theorem UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by
  intro G M _ _ ρ σ hσ x hx g
  have h0 : ρ σ x - x = 0 := hx
  have h1 : ρ σ x = x := sub_eq_zero.mp h0
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by
            rw [inv_mul_cancel, map_one]
            rfl }
  have hle : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr h1
  exact hle (hσ g)
