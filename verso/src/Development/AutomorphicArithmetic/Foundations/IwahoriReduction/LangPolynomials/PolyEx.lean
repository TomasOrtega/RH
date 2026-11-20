import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertiaStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Kd.C7.pPolyEx :
    UpperTheory.Kd.C7.SPolyEx := by
  intro l _ _ Ω _ _ _ A hA ζ hζ m u hu hinv
  obtain ⟨P, hP, hev⟩ := GlobalTheory.T.exists_polynomial_primitiveRoot_of_cyclotomic_inertia_fixed l Ω A hA m (ζ m) (hζ m).1 u hu
    (fun s hs h1 => hinv s ⟨hs, MonoidHom.mem_ker.2 h1⟩)
  have hsub : (↑P.coeffs : Set Ω) ⊆ (R0 A : Set Ω) := fun z hz => hP z hz
  refine ⟨P.toSubring (R0 A) hsub, ?_⟩
  unfold pv
  rw [← Polynomial.eval_map, Polynomial.map_toSubring, hev]
