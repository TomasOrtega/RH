import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCovolumeEqSelfDualLatticesSameHermitianSpace.lean&line=340#L340)
-/
theorem _root_.GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  first | exact @GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space | exact GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space | (intros; apply GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space <;> assumption)
