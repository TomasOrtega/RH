import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.RcChars
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinSph
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharConjInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharacterPlusPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicSolutionParallel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SignAtInfinityOfParallelWeight

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

/- English proof (translation)
Use `haveI : IsAlgClosure (maximalRealSubfield K) Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩`. Take `⟨μ, χ, c, P, hμ, hs, hc, hP⟩` from `UpperTheory.cyclotomicCharacter_plusPart (algOfCyc H) UpperTheory.cyclotomic_char_conj_invariant K Ω l ι n r hp`. Establish `hdual` using `selfDualC H K Ω l ι n hn r π ha χ μ hμ c P hc hP`. Establish `hsign` using `UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs`. Take `⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K))` from `inferInstance`.

Establish `hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by`. Break down `sq_eq_one_iff.1 hsq with e | e` into its components or cases. Conclude with `⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩`.

Conclude with `⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩`. Establish `hnorm : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ`. Rewrite using `[map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]`. Use `⟨χ * quadChar K ^ (m + n), fun v => ?_, hnorm ▸ hdual⟩` and prove the remaining obligations. Rewrite using `[HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]`.

Simplify using the standard rewrite rules.
-/
private theorem exists_polarized {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (H : HypothesesH) {ι : Qbar l ≃+* ℂ} (hn : 1 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hp : Sol.Pol ι r) (ha : AttC ι r π) : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := UpperTheory.cyclotomicCharacter_plusPart (algOfCyc H) UpperTheory.cyclotomic_char_conj_invariant K Ω l ι n r hp
  have hdual := selfDualC H K Ω l ι n hn r π ha χ μ hμ c P hc hP
  have hsign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    rcases sq_eq_one_iff.1 hsq with e | e
    · exact ⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
  have hnorm : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  refine ⟨χ * quadChar K ^ (m + n), fun v => ?_, hnorm ▸ hdual⟩
  rw [HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
  simp

/- English proof (translation)
Take `⟨g, rfl⟩` from `ha.surj x`. Establish `h0 : deg g = 0`. Use `ha.ord_eq g` as an intermediate fact. Rewrite `this` using `[hx]`. Use linear arithmetic over natural numbers and integers.

Establish `e` using `congrArg (Polynomial.eval ((ξ j (a g) : ℂˣ) : ℂ)) (H g h0)`. Rewrite `e` using `[Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp)]`. Establish `e2 : ((ξ j (a g) : ℂˣ) : ℂ) - 1 = 0`. Use `e.symm` as an intermediate fact. Simplify using `only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at this`.

Conclude with `(pow_eq_zero_iff j.pos.ne').1 this`. Conclude with `Units.ext (by simpa [sub_eq_zero] using e2)`.
-/
private theorem unram_of_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {n : ℕ} (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ))
    (H : ∀ g : Weil h, deg g = 0 → ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) = (X - 1 : ℂ[X]) ^ n) (j : Fin n)
    (x : (w.adicCompletion E)ˣ) (hx : ord (w.adicCompletion E) x = 0) : ξ j x = 1 := by
  obtain ⟨g, rfl⟩ := ha.surj x
  have h0 : deg g = 0 := by
    have := ha.ord_eq g
    rw [hx] at this
    omega
  have e := congrArg (Polynomial.eval ((ξ j (a g) : ℂˣ) : ℂ)) (H g h0)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp)] at e
  have e2 : ((ξ j (a g) : ℂˣ) : ℂ) - 1 = 0 := by
    have := e.symm
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at this
    exact (pow_eq_zero_iff j.pos.ne').1 this
  exact Units.ext (by simpa [sub_eq_zero] using e2)

end UpperTheory.V.Z.Win.Birth
