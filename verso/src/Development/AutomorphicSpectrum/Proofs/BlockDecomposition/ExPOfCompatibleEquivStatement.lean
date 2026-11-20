import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquiv
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExPOfCompatibleEquiv.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exP_of_compatible_equiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv <;> assumption)
