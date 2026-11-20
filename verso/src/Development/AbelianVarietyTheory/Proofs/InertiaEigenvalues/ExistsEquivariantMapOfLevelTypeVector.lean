import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

/- English proof (translation)
Introduce `hp hy`. Take `⟨h1, ℓ, hℓ, h0⟩` from `hy`. Set `Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W)` to `fun μ => ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)`. Establish `hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y`. Introduce `μ w`.

Simplify using `[Φ, LinearMap.sum_apply]`. Establish `heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w)`. Introduce `μ g₀ h H w`. Rewrite using `[hΦ, hΦ, map_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]`. Simplify using `[mul_inv_rev, map_mul, Module.End.mul_apply]`. Assume the negation of the conclusion as `hne`. Establish `hz : ∀ μ, Φ μ = 0` using `fun μ => by`. Assume the negation of the conclusion as `e`.

Conclude with `hne ⟨_, e, heq μ⟩`. Apply `h0` to reduce the goal to its premises. Set `b` to `Module.finBasis ℂ ρ`. Establish `key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0`. Establish `: ∑ i, Φ (b.coord i) (b i) = 0` using `by simp [hz]`.

Rewrite using `[← this]`. Repeatedly rewrite using `[hΦ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply]`. Both sides reduce to the same expression. Rewrite using `[Finsupp.sum_fintype _ _ (by simp)]`.

Repeatedly rewrite using `[Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]`. Rewrite using `[← Finset.smul_sum, key, smul_zero]`.
-/
theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w
    rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
