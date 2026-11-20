import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem mem_princ_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : G ℚ Ω) : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ g ∈ (galChar Ω (l ^ n)).ker := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ ℚ Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  rw [h1, cyclotomicCharacter.toZModPow, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Two.levChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (U : Subgroup (G ℚ Ω)), levU l U n = U ⊓ (galChar Ω (l ^ n)).ker ∧ (cycZ ℚ Ω l).ker ≤ (galChar Ω (l ^ n)).ker := by
  intro Ω _ _ _ l _ n U
  refine ⟨?_, fun g hg => ?_⟩
  · ext g
    rw [levU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, mem_princ_iff]
  · rw [← mem_princ_iff, MonoidHom.mem_ker.1 hg]
    exact one_mem _
