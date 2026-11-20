import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleSequenceExact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPhiKNil
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDvdOfNil

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.Ru.crystallineComparison.nilToPhi :
    UpperTheory.Ru.crystallineComparison.NilToPhi := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hcr Q hN s u hu hQ
  refine ⟨(GlobalTheory.Pst.IsModel.isCrysAt_iff P hm).2 hcr, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.phiKNil_of UpperTheory.Gal.crystallineComparison.dvdOfNil_of UpperTheory.Gal.crystallineComparison.nilWeil_of
    UpperTheory.Gal.crystallineComparison.nilRho_of UpperTheory.Gal.crystallineComparison.wdModel_of l P AI hT ι E Ω A w h O Bw hj a r LL r' hm hcr
    Q hN s u hu hQ
