import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.Int.Geo (KS Lv Sc)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.kSProj_of :
    ZSm → ZPr → KSProj := by
  intro hSm hPr p _ D G L hSc gb k T N
  have hq : qAt T N = (T.e N).hom ≫ ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s) := (T.e_q N).symm
  rw [hq]
  constructor
  · obtain ⟨M, i, hi, hi'⟩ := hPr p D hSc.cpt gb N.1 N.2.1 N.2.2 (T.M N) k
    refine ⟨M, (T.e N).hom ≫ i, ?_, ?_⟩
    · haveI := hi
      infer_instance
    · rw [Category.assoc, hi']
  · obtain ⟨d, hd⟩ := hSm D.toG gb N.1 N.2.1 (T.M N) k
    haveI := hd
    have h0 : SmoothOfRelativeDimension 0 (T.e N).hom := inferInstance
    have h2 := AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := d) (T.e N).hom
      ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s)
    rw [zero_add] at h2
    exact ⟨d, h2⟩
