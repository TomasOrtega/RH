import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMassMulVolumeCommensurable.lean&line=212#L212)
-/
theorem _root_.GlobalTheory.T.mass_mul_volume_commensurable : ∀ {G : Type} [Group G] (Γ' T C C' : Subgroup G), C ≤ T → C' ≤ T → C.relIndex C' ≠ 0 → C'.relIndex C ≠ 0 → (∀ t ∈ T, ((Γ' ⊓ C.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → (∀ t ∈ T, ((Γ' ⊓ C'.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → massC Γ' T C' * vol C C' = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.MassChange.massC_mul_vol | exact GlobalTheory.LKCount.MassChange.massC_mul_vol | (intros; apply GlobalTheory.LKCount.MassChange.massC_mul_vol <;> assumption)
