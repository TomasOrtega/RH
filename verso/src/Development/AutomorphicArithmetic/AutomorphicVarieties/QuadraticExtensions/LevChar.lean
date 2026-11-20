import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Establish `e : cycZ ℚ Ω l g = cyclotomicCharacter Ω l g.toRingEquiv` using `rfl`. Establish `h1 : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1`.

Rewrite using `[KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]`. Both sides reduce to the same expression. Rewrite using `[h1, cyclotomicCharacter.toZModPow, MonoidHom.mem_ker, Units.ext_iff]`. Both sides reduce to the same expression.
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
Introduce `Ω _ _ _ l _ n U`. Use `⟨?_, fun g hg => ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Rewrite using `[levU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, mem_princ_iff]`. Rewrite using `[← mem_princ_iff, MonoidHom.mem_ker.1 hg]`.

Conclude with `one_mem _`.
-/
theorem UpperTheory.V.Two.levChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (U : Subgroup (G ℚ Ω)), levU l U n = U ⊓ (galChar Ω (l ^ n)).ker ∧ (cycZ ℚ Ω l).ker ≤ (galChar Ω (l ^ n)).ker := by
  intro Ω _ _ _ l _ n U
  refine ⟨?_, fun g hg => ?_⟩
  · ext g
    rw [levU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, mem_princ_iff]
  · rw [← mem_princ_iff, MonoidHom.mem_ker.1 hg]
    exact one_mem _
