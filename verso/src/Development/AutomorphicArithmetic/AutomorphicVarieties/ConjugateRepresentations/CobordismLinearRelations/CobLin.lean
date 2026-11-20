import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem geo_hd_smul_add {Γ M : Type} [AddCommGroup M] [Module ℂ M] (s : ℂ)
    (b b' : List Γ → M) (x : List Γ) :
    UpperTheory.V.Lit.Geo.hd (s • b + b') x =
      s • UpperTheory.V.Lit.Geo.hd b x + UpperTheory.V.Lit.Geo.hd b' x := by
  unfold UpperTheory.V.Lit.Geo.hd
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, Pi.smul_apply, smul_add, smul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Treat this case separately. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.Cj.cobLin :
    UpperTheory.V.Cj.CobLin := by
  intro Γ M _ _ _ ρ q s c c' hc hc'
  cases q with
  | zero =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    intro x hx
    rw [Pi.add_apply, Pi.smul_apply, hc x hx, hc' x hx, smul_zero, add_zero]
  | succ k =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    obtain ⟨b, hbe, hbc⟩ := hc
    obtain ⟨b', hbe', hbc'⟩ := hc'
    refine ⟨s • b + b', fun γ x hx => ?_, fun x hx => ?_⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, hbe γ x hx, hbe' γ x hx,
        map_add, map_smul]
    · rw [geo_hd_smul_add, Pi.add_apply, Pi.smul_apply, hbc x hx, hbc' x hx]
