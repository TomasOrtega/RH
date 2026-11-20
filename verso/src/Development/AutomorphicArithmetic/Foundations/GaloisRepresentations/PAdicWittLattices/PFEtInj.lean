import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.G3.pFEtInj :
    GalClosD → FEtInj.{u} := by
  intro hGC B R _ T hT Z W p r c hc d hd hfet
  obtain ⟨V, e, G, _, _, a, σ, hgal, hspl⟩ := hGC c d hfet
  have h0 : σ ⟨0, hd⟩ ≫ c = e := hspl.1 _
  subst h0
  have hinj := hT.inj p ((σ ⟨0, hd⟩ ≫ c) ≫ p) (σ ⟨0, hd⟩ ≫ c) rfl G a hgal
  have hσr : σ ⟨0, hd⟩ ≫ r = (σ ⟨0, hd⟩ ≫ c) ≫ p := by
    rw [← hc, Category.assoc]
  have hcomp := T.pull_comp (σ ⟨0, hd⟩) c hσr hc rfl
  intro x y hxy
  apply hinj
  rw [hcomp x, hcomp y, hxy]
