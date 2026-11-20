import Mathlib

noncomputable def UpperTheory.Reformulated.B.Rb1.Zc :
    {D N : Type} → [inst : Group D] → [TopologicalSpace D] → [inst_2 : AddCommGroup N] → Representation ℤ D N → Set (D → N) :=
    fun {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) ↦
      {z : D → N | IsLocallyConstant z ∧ ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t)}

/- English proof (translation)
Introduce `D N _ _ _ _ ρ I φ hcl z hz hI hφ s`. Establish `hlc : IsLocallyConstant z` using `hz.1`. Establish `hco : ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t)` using `hz.2`. Establish `h1 : z 1 = 0`. Establish `h` using `hco 1 1`.

Rewrite `h` using `[mul_one, map_one]`. Simplify using `using h`. Set `K : Subgroup D` to `{ carrier := z ⁻¹' {0} mul_mem' := by`. Introduce `a b ha hb`. Establish `ha' : z a = 0` using `ha`.

Establish `hb' : z b = 0` using `hb`. Use `show z (a * b) = 0`. Rewrite using `[hco, ha', hb', map_zero, add_zero]`. Use the proof step `one_mem' := h1`. Use the proof step `inv_mem' := by`.

Introduce `a ha`. Establish `ha' : z a = 0` using `ha`. Use `show z a⁻¹ = 0`. Establish `h` using `hco a⁻¹ a`. Rewrite `h` using `[inv_mul_cancel, h1, ha', map_zero, add_zero]`.

Conclude with `h.symm }`. Establish `hK : IsClosed (K : Set D)` using `hlc.isClosed_fiber 0`. Establish `hle : I ⊔ Subgroup.zpowers φ ≤ K` using `sup_le hI (by`. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `hφ)`.

Establish `htop : (⊤ : Subgroup D) ≤ K`. Rewrite using `[← hcl]`. Conclude with `Subgroup.topologicalClosure_minimal _ hle hK`. Conclude with `htop (Subgroup.mem_top s)`.
-/
theorem UpperTheory.Reformulated.B.Rb1.ul_zero :
    ∀ {D N : Type} [inst : Group D] [inst_1 : TopologicalSpace D] [inst_2 : IsTopologicalGroup D] [inst_3 : AddCommGroup N]
      (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
        ∀ z ∈ UpperTheory.Reformulated.B.Rb1.Zc ρ, (∀ s ∈ I, z s = (0 : N)) → z φ = (0 : N) → ∀ (s : D), z s = (0 : N) := by
  intro D N _ _ _ _ ρ I φ hcl z hz hI hφ s
  have hlc : IsLocallyConstant z := hz.1
  have hco : ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t) := hz.2
  have h1 : z 1 = 0 := by
    have h := hco 1 1
    rw [mul_one, map_one] at h
    simpa using h
  let K : Subgroup D :=
    { carrier := z ⁻¹' {0}
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = 0 := ha
        have hb' : z b = 0 := hb
        show z (a * b) = 0
        rw [hco, ha', hb', map_zero, add_zero]
      one_mem' := h1
      inv_mem' := by
        intro a ha
        have ha' : z a = 0 := ha
        show z a⁻¹ = 0
        have h := hco a⁻¹ a
        rw [inv_mul_cancel, h1, ha', map_zero, add_zero] at h
        exact h.symm }
  have hK : IsClosed (K : Set D) := hlc.isClosed_fiber 0
  have hle : I ⊔ Subgroup.zpowers φ ≤ K :=
    sup_le hI (by
      rw [Subgroup.zpowers_le]
      exact hφ)
  have htop : (⊤ : Subgroup D) ≤ K := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hK
  exact htop (Subgroup.mem_top s)
