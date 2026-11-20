import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCompleteDvrExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCountableCompleteDvrExtension.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_countable_complete_dvr_extension : ∀ (A V : Type) [CommRing A] [IsLocalRing A] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (φ : A →+* V), Countable A → IsLocalHom φ → (∃ a ∈ maximalIdeal A, φ a ≠ 0) → ∃ (T : Formalism.L2.Pj.CDVR) (ψ : A →+* T.V), IsLocalHom ψ ∧ RingHom.ker ψ = RingHom.ker φ ∧ Cardinal.mk T.V ≤ Cardinal.continuum := by
  first | exact @GlobalTheory.SmallDVR.exists_small_cdvr_of_localHom | exact GlobalTheory.SmallDVR.exists_small_cdvr_of_localHom | (intros; apply GlobalTheory.SmallDVR.exists_small_cdvr_of_localHom <;> assumption)
