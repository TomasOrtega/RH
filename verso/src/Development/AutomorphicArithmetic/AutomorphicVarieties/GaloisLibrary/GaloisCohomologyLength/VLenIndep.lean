import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ D D' e`. Establish `hS : D.S = D'.S` using `Finset.coe_injective (D.hS.trans D'.hS.symm)`. Use `⟨hS, ?_⟩` and prove the remaining obligations. Take `⟨S, hS₁, A, hA, chi, hchi⟩` from `D`. Take `⟨S', hS₂, A', hA', chi', hchi'⟩` from `D'`.

Simplify using `only at hS`. Substitute `hS` using the available equality. Establish `hc : chi = chi'`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`.

Conclude with `DFunLike.congr_fun (hchi.trans hchi'.symm) g`. Substitute `hc` using the available equality. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.LDataCardLeFinrank.vLenIndep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D D' : LData F Ω l) (e : ℤ), D.S = D'.S ∧ VLen D e = VLen D' e := by
  intro F Ω _ _ _ _ _ l _ D D' e
  have hS : D.S = D'.S := Finset.coe_injective (D.hS.trans D'.hS.symm)
  refine ⟨hS, ?_⟩
  obtain ⟨S, hS₁, A, hA, chi, hchi⟩ := D
  obtain ⟨S', hS₂, A', hA', chi', hchi'⟩ := D'
  dsimp only at hS
  subst hS
  have hc : chi = chi' := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact DFunLike.congr_fun (hchi.trans hchi'.symm) g
  subst hc
  rfl
