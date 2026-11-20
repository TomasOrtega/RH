import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Gen.smoothAt_pf :
    UpperTheory.Gal.Gen.SmoothAt := by
  intro E _ _ _ a w₀ hw W f
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let p : GL (Fin a) (w₀.adicCompletion E) → finU E a := fun y =>
    ⟨(e.symm y).1, (Subgroup.mem_inf.1 (e.symm y).2).1⟩
  have hp : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp e.symm.continuous) _
  have hp1 : p 1 = 1 := by
    apply Subtype.ext
    simp [p]
  have hS : IsOpen {k : finU E a | algRep W k f = f} := GlobalTheory.DefU.isSmooth_algRep W f
  refine ⟨p ⁻¹' {k : finU E a | algRep W k f = f},
    (hS.preimage hp).mem_nhds (by simp [hp1]), fun x hx hxN v g => ?_⟩
  have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
    rw [← he ⟨x, hx⟩]
    exact e.symm_apply_apply _
  have h2 : algRep W (p (cLoc w₀ x)) f = f := hxN
  have h3 : (p (cLoc w₀ x)).1 = x := by
    simp only [p, h1]
  have h4 := congrArg (fun F : algForms W => F.1 v g) h2
  change f.1 v (g * (p (cLoc w₀ x)).1) = f.1 v g at h4
  rwa [h3] at h4
