import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import GroundTheory.LocalFields.UnramifiedNormSurj
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitNormUnr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem normU : Ad3.K.QuadraticBaseChangeGL3.Th.NORMU := by
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ hd hc σ _ η _ hres u hu hu'
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.NormModulus.valuativeExtension_of_continuous hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hdeg : residueDegree F E = 2 := by
    have h := card_residueField_eq_pow_residueDegree F E
    have h' : residueCard E = residueCard F ^ residueDegree F E := h
    rw [hres] at h'
    exact (Nat.pow_right_injective (one_lt_residueCard (K := F))  h').symm
  haveI : IsUnramified F E :=
    (isUnramified_iff_residueDegree_eq_finrank F E).2 (hdeg.trans hd.symm)
  let h : 𝒪[F]ˣ :=
    ⟨⟨u, hu⟩, ⟨_, hu'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  obtain ⟨g, hg⟩ := normIntegerUnits_surjective (K := F) (L := E) h
  refine ⟨unitsIncl E g, ?_⟩
  rw [← coe_normUnits, normUnits_unitsIncl, hg]
  rfl

end GlobalTheory.CompanionTheory.UnitNormUnr
