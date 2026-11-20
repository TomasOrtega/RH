import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeviRestrictionSmooth.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.levi_restriction_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ), F ∈ Sm E (r + s) → (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | exact GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice <;> assumption)
