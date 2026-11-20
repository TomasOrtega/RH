import Mathlib

open Polynomial Matrix

/- English proof (translation)
Introduce `K G ι _ _ _ _ ρ ρ' P Q hs hP h1 h2`. Take `⟨U, rfl⟩` from `hP`. Establish `key : ∀ M : Matrix ι ι K, M * ((↑U⁻¹ : Matrix ι ι K) * Q) = ((↑U⁻¹ : Matrix ι ι K) * Q) * M`. Introduce `M`. Establish `hM : M ∈ Submodule.span K (Set.range ρ)` using `hs ▸ Submodule.mem_top`.

Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`. Establish `e : ρ g * (↑U⁻¹ : Matrix ι ι K) = (↑U⁻¹ : Matrix ι ι K) * ρ' g`. Rewrite using `[Units.eq_inv_mul_iff_mul_eq, ← mul_assoc, h1, mul_assoc, Units.mul_inv, mul_one]`.

Rewrite using `[← mul_assoc, e, mul_assoc, mul_assoc, h2]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]`. Consider the case `smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]`. Take `⟨c, hc⟩` from `Matrix.mem_range_scalar_of_commute_single (M := (↑U⁻¹ : Matrix ι ι K) * Q) fun i j _ => key _`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `: Q = (U : Matrix ι ι K) * ((↑U⁻¹ : Matrix ι ι K) * Q)` using `by rw [← mul_assoc, Units.mul_inv, one_mul]`. Rewrite using `[this, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, mul_smul_comm, mul_one]`.
-/
theorem UpperTheory.V.AlgebraTools.Det.schurLine :
    ∀ {K G ι : Type} [Field K] [Monoid G] [Fintype ι] [DecidableEq ι] (ρ ρ' : G →* Matrix ι ι K) (P Q : Matrix ι ι K),
    Submodule.span K (Set.range ρ) = ⊤ → IsUnit P → (∀ g, P * ρ g = ρ' g * P) → (∀ g, Q * ρ g = ρ' g * Q) → ∃ c : K, Q = c • P := by
  intro K G ι _ _ _ _ ρ ρ' P Q hs hP h1 h2
  obtain ⟨U, rfl⟩ := hP
  have key : ∀ M : Matrix ι ι K, M * ((↑U⁻¹ : Matrix ι ι K) * Q) = ((↑U⁻¹ : Matrix ι ι K) * Q) * M := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ρ) := hs ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have e : ρ g * (↑U⁻¹ : Matrix ι ι K) = (↑U⁻¹ : Matrix ι ι K) * ρ' g := by
        rw [Units.eq_inv_mul_iff_mul_eq, ← mul_assoc, h1, mul_assoc, Units.mul_inv, mul_one]
      rw [← mul_assoc, e, mul_assoc, mul_assoc, h2]
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := (↑U⁻¹ : Matrix ι ι K) * Q) fun i j _ => key _
  refine ⟨c, ?_⟩
  have : Q = (U : Matrix ι ι K) * ((↑U⁻¹ : Matrix ι ι K) * Q) := by rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [this, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, mul_smul_comm, mul_one]
