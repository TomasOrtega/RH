import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RynePlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Psdcone

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KT.good :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ), ConeExtensionAcyclic.Good (qc L N) (Psd L N) := by
  intro L _ _ _ N
  obtain ⟨hc, hs, hp, hd⟩ := psdcone L N
  refine ⟨fun h hh => ?_, ?_, hc, hs, ?_, hd⟩
  · rw [poly_qc] at hh
    obtain ⟨S, hS, hev⟩ := locfin L N h (rypos L N hh) 1
    refine ⟨Subtype.val ⁻¹' S, hS.preimage Subtype.val_injective.injOn, ?_⟩
    filter_upwards [hev] with k hk y hy
    exact hk y.1 hy
  · rw [poly_qc]; exact ryne L N
  · rw [poly_qc]; exact (rypos L N).trans hp
