import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FinChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Z.Win
open UpperTheory.V.Z.Win.Dn

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ n r h v hv A hA`. Establish `hn : ¬ A.valuation (l : Ω) < 1` using `fun e => hv ((hA _).1 (by simpa using e))`. Take `⟨χ, hc, hf, hk⟩` from `h A hn`. Take `⟨j, hj⟩` from `UpperTheory.V.Lib.FinChar.charpoly_of_ker r χ (Ine (F := F) A) hf hk`. Use `⟨fun i => (χ.comp (Dec (F := F) A).subtype) ^ j i, fun i => ?_, fun g hg => ?_⟩` and prove the remaining obligations.

Conclude with `(hc.comp continuous_subtype_val).pow (j i)`. Use `(hj _ hg).trans (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Win.Dn.ineOfKer_of :
    IneOfKer := by
  intro F Ω _ _ _ _ _ l _ n r h v hv A hA
  have hn : ¬ A.valuation (l : Ω) < 1 := fun e => hv ((hA _).1 (by simpa using e))
  obtain ⟨χ, hc, hf, hk⟩ := h A hn
  obtain ⟨j, hj⟩ := UpperTheory.V.Lib.FinChar.charpoly_of_ker r χ (Ine (F := F) A) hf hk
  refine ⟨fun i => (χ.comp (Dec (F := F) A).subtype) ^ j i, fun i => ?_, fun g hg => ?_⟩
  · exact (hc.comp continuous_subtype_val).pow (j i)
  · refine (hj _ hg).trans (Finset.prod_congr rfl fun i _ => ?_)
    simp
