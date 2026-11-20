import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem residueField_isAlgebraic_of_etale :
    ∀ {A B : Type} [CommRing A] [CommRing B] (g : A →+* B), g.Etale →
    ∀ (P : Ideal B) [P.IsPrime],
    @Algebra.IsAlgebraic (P.comap g).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra := by
  intro A B _ _ g hg P _
  letI := g.toAlgebra
  have hE : Algebra.Etale A B := RingHom.etale_algebraMap.mp hg
  haveI : P.LiesOver (P.comap g) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (P.comap g) P
  haveI : Localization.AtPrime.IsLiesOverAlgebra (P.comap g) P := ⟨rfl⟩
  haveI : Algebra.EssFiniteType A B := inferInstance
  haveI : Algebra.IsUnramifiedAt A P := inferInstance
  have hsep : Algebra.IsSeparable (P.comap g).ResidueField P.ResidueField := inferInstance
  have halg := hsep.isAlgebraic
  convert halg using 1
  apply Algebra.algebra_ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  induction y using Localization.induction_on with
  | H y =>
    obtain ⟨a, s⟩ := y
    simp [Ideal.ResidueField.map, RingHom.algebraMap_toAlgebra, Localization.AtPrime.algebraOfLiesOver, Localization.mk_eq_mk']

end GlobalTheory
