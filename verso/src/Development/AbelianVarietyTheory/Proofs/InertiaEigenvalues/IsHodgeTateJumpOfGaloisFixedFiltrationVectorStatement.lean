import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKGal.isJumpV_of_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsHodgeTateJumpOfGaloisFixedFiltrationVector.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  first | exact @GlobalTheory.BKGal.isJumpV_of_fixed | exact GlobalTheory.BKGal.isJumpV_of_fixed | (intros; apply GlobalTheory.BKGal.isJumpV_of_fixed <;> assumption)
