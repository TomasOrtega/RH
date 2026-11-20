import Mathlib

namespace GlobalTheory.AdTh

/- English proof (translation)
Establish `hu : IsUnit (T : Module.End ℂ M)` using `(Module.End.isUnit_iff _).2 ⟨hT, LinearMap.injective_iff_surjective.1 hT⟩`. Take `⟨u, hu⟩` from `hu`. Establish `h1 : ∀ γ, (u : Module.End ℂ M) * ρ γ = χ γ • (ρ γ * u)`. Introduce `γ`. Use extensionality with `x`.

Simplify using `[hu, h]`. Establish `hχ : ∀ γ ∈ S, χ γ = 1`. Introduce `γ hγ`. Establish `h2 : (u : Module.End ℂ M) * ρ γ * (↑u⁻¹ : Module.End ℂ M) = χ γ • ρ γ`. Rewrite using `[h1, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]`.

Establish `h3` using `congrArg (LinearMap.trace ℂ M) h2`. Rewrite `h3` using `[LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, map_smul, smul_eq_mul]`. Establish `h4` using `htr γ hγ`. Establish `: (χ γ - 1) * LinearMap.trace ℂ M (ρ γ) = 0` using `by linear_combination -h3`. Break down `mul_eq_zero.1 this with h5 | h5` into its components or cases.

Conclude with `sub_eq_zero.1 h5`. Conclude with `absurd h5 h4`. Establish `hc : ∀ γ, Commute (u : Module.End ℂ M) (ρ γ)`. Introduce `γ`. Establish `hγ : γ ∈ Subgroup.closure S` using `hS ▸ Subgroup.mem_top γ`.

Proceed by induction on `hγ using Subgroup.closure_induction with`. Consider the case `mem x hx`. Use `h1 x` as an intermediate fact. Rewrite `this` using `[hχ x hx, one_smul]`. Conclude with `this`.

Consider the case `one => rw [map_one]`. Conclude with `Commute.one_right _`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `hx.mul_right hy`. Consider the case `inv x _ hx`.

Establish `e1 : ρ x * ρ x⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `e2 : ρ x⁻¹ * ρ x = 1` using `by rw [← map_mul, inv_mul_cancel, map_one]`. Conclude with `Commute.units_inv_right (u := ⟨ρ x, ρ x⁻¹, e1, e2⟩) hx`. Take `⟨a, ha⟩` from `Module.End.exists_eigenvalue (T : Module.End ℂ M)`. Use `⟨a, fun x => ?_⟩` and prove the remaining obligations.

Break down `hirr (Module.End.eigenspace T a) (by` into its components or cases. Introduce and unpack `γ _ ⟨y, hy, rfl⟩`. Establish `hy' : T y = a • y` using `Module.End.mem_eigenspace_iff.1 hy`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Use `congrArg (fun f : Module.End ℂ M => f y) (hc γ).eq` as an intermediate fact.

Simplify using `only [hu, Module.End.mul_apply] at this`. Rewrite using `[this, hy', map_smul]) with h0 | h0`. Conclude with `absurd h0 (Module.End.hasEigenvalue_iff.1 ha)`. Conclude with `Module.End.mem_eigenspace_iff.1 (h0 ▸ Submodule.mem_top)`.
-/
theorem scalar_of_intertwines_up_to_scalar (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [Nontrivial M] (ρ : Γ →* Module.End ℂ M) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (htr : ∀ γ ∈ S, LinearMap.trace ℂ M (ρ γ) ≠ 0)
    (hirr : ∀ U : Submodule ℂ M, (∀ γ, U.map (ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤)
    (T : M →ₗ[ℂ] M) (χ : Γ → ℂ) (hT : Function.Injective T)
    (h : ∀ γ x, T (ρ γ x) = χ γ • ρ γ (T x)) : ∃ a : ℂ, ∀ x, T x = a • x := by
  have hu : IsUnit (T : Module.End ℂ M) :=
    (Module.End.isUnit_iff _).2 ⟨hT, LinearMap.injective_iff_surjective.1 hT⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ∀ γ, (u : Module.End ℂ M) * ρ γ = χ γ • (ρ γ * u) := by
    intro γ
    ext x
    simp [hu, h]
  have hχ : ∀ γ ∈ S, χ γ = 1 := by
    intro γ hγ
    have h2 : (u : Module.End ℂ M) * ρ γ * (↑u⁻¹ : Module.End ℂ M) = χ γ • ρ γ := by
      rw [h1, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    have h3 := congrArg (LinearMap.trace ℂ M) h2
    rw [LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, map_smul, smul_eq_mul] at h3
    have h4 := htr γ hγ
    have : (χ γ - 1) * LinearMap.trace ℂ M (ρ γ) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 this with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 h4
  have hc : ∀ γ, Commute (u : Module.End ℂ M) (ρ γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      have := h1 x
      rw [hχ x hx, one_smul] at this
      exact this
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx =>
      have e1 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e2 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact Commute.units_inv_right (u := ⟨ρ x, ρ x⁻¹, e1, e2⟩) hx
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ M)
  refine ⟨a, fun x => ?_⟩
  rcases hirr (Module.End.eigenspace T a) (by
      rintro γ _ ⟨y, hy, rfl⟩
      have hy' : T y = a • y := Module.End.mem_eigenspace_iff.1 hy
      rw [Module.End.mem_eigenspace_iff]
      have := congrArg (fun f : Module.End ℂ M => f y) (hc γ).eq
      simp only [hu, Module.End.mul_apply] at this
      rw [this, hy', map_smul]) with h0 | h0
  · exact absurd h0 (Module.End.hasEigenvalue_iff.1 ha)
  · exact Module.End.mem_eigenspace_iff.1 (h0 ▸ Submodule.mem_top)

end GlobalTheory.AdTh
