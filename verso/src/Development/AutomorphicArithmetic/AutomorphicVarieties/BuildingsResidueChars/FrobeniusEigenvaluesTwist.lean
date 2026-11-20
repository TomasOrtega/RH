import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Establish `hc : Multiset.card L = Fintype.card ι`. Rewrite using `[← Matrix.charpoly_natDegree_eq_dim M, hM, natDegree_multiset_prod_X_sub_C_eq_card]`. Break down `eq_or_ne u 0 with rfl | hu` into its components or cases. Simplify using `[hc]`. Use `Polynomial.funext fun x => ?_` and prove the remaining obligations.

Establish `h1` using `congrArg (eval (x / u)) hM`. Rewrite `h1` using `[Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map]`. Establish `e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M)`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Simplify using `[Matrix.diagonal_apply_ne _ hab]`. Rewrite using `[Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map, Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]`.

Use `congrArg _ (Multiset.map_congr rfl fun α _ => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.
-/
private theorem charpoly_smul_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (hM : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  have hc : Multiset.card L = Fintype.card ι := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hM, natDegree_multiset_prod_X_sub_C_eq_card]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

/- English proof (translation)
Introduce `F Ω _ _ _ _ l _ ι n r δ w B z hr hδ A hA`. Take `⟨h1, h2⟩` from `hr A hA`. Take `⟨h3, h4⟩` from `hδ A hA`. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[tw_val, h1 s hs, h3 s hs]`. Simplify using the standard rewrite rules. Establish `e1` using `h2 σ hσ`. Establish `e2` using `h4 σ hσ`. Rewrite `e1`, the goal using `[← Matrix.charpoly_map]`.

Rewrite using `[← charpoly_smul_prod _ z B e1, tw_val, ← e2]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.frobenius_eigenvalues_twist :
    UpperTheory.V.Af.Bc.FrobTw := by
  intro F Ω _ _ _ _ l _ ι n r δ w B z hr hδ A hA
  obtain ⟨h1, h2⟩ := hr A hA
  obtain ⟨h3, h4⟩ := hδ A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    rw [tw_val, h1 s hs, h3 s hs]
    simp
  · have e1 := h2 σ hσ
    have e2 := h4 σ hσ
    rw [← Matrix.charpoly_map] at e1 ⊢
    rw [← charpoly_smul_prod _ z B e1, tw_val, ← e2]
    congr 1
    ext i j
    simp
