import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.Int.Geo.pieceStab_of :
    HopGal → PieceStab := by
  intro hG l _ k _ hl H hfet Ω _ _ L _ _ θ σ x hx
  simp only [piece, Submodule.mem_iInf] at hx ⊢
  intro g
  obtain ⟨d, hd⟩ := hfet g
  have hc := hG l k hl H Ω g d hd σ
  have hxg := hx g
  rw [Module.End.mem_eigenspace_iff] at hxg ⊢
  have e : (LinearMap.baseChange L (hop l H Ω g)) ((galV l H Ω L σ) x)
      = (galV l H Ω L σ) ((LinearMap.baseChange L (hop l H Ω g)) x) := by
    show ((LinearMap.baseChange L (hop l H Ω g)) ∘ₗ (LinearMap.baseChange L (galTot l Ω H.q σ))) x
      = ((LinearMap.baseChange L (galTot l Ω H.q σ)) ∘ₗ (LinearMap.baseChange L (hop l H Ω g))) x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  rw [e, hxg, map_smul]
