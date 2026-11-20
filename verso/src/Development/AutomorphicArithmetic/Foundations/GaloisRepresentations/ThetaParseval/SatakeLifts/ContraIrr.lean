import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqMapBijective
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem UpperTheory.Gal.TP.Loc.contraIrr :
    UpperTheory.Gal.TP.Loc.ContraIrr := by
  intro k _ _ _ _ n V _ _ ρ hs hi
  have hadm := (GlobalTheory.Laid.bzfin_holds k).1 (Fin n) V ρ hs hi
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k n
  exact ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm hi, ⟨GlobalTheory.ContraRefl.evEquiv hG hadm⟩⟩
