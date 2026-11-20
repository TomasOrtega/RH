import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOne
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UTrans.tvGen_normal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FUnitaryTransvectionSubmonoidNormalDetOne.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  first | exact @GlobalTheory.UTrans.tvGen_normal | exact GlobalTheory.UTrans.tvGen_normal | (intros; apply GlobalTheory.UTrans.tvGen_normal <;> assumption)
