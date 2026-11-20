import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem UpperTheory.Gal.crystallineComparison.unrGeom_of :
    UnrOfGeom := by
  classical
  intro E Ω _ _ _ _ _ A w h x y hx hy g hg hxy
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hx
  obtain ⟨m, d, rfl⟩ := Unram.exists_diag hy
  rw [WD.charPol_mk, WD.charPol_mk, WDRep.diag_ρ, WDRep.diag_ρ, charpoly_diagEnd, charpoly_diagEnd, hg] at hxy
  have key := congrArg Polynomial.roots hxy
  simp only [Finset.prod_eq_multiset_prod] at key
  have R : ∀ {k : ℕ} (e : Fin k → ℂˣ),
      (Multiset.map (fun i => Polynomial.X - Polynomial.C (((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))) Finset.univ.val).prod.roots =
        Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ) := by
    intro k e
    have := Polynomial.roots_multiset_prod_X_sub_C
      (Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))
    rwa [Multiset.map_map] at this
  rw [R, R] at key
  apply Unram.diag_eq_diag
  have := congrArg (Multiset.map fun z : ℂ => z⁻¹) key
  simpa [Multiset.map_map, Function.comp_def, zpow_neg_one, inv_inv] using this
