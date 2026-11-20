import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

/- English proof (translation)
Introduce `X _ U hU z hz h`. Use `haveI : Nonempty U := ⟨⟨z, hz⟩⟩`. Use `letI := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)`. Use `haveI := hU.isLocalization_stalk ⟨z, hz⟩`. Establish `hc : (hU.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1`.

Use `IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨z, hz⟩).asIdeal (X.presheaf.stalk z)` as an intermediate fact. Rewrite `this` using `[ringKrullDim_stalk_eq_coheight, h]`. Conclude with `this.symm` after adjusting the coercions. Use `⟨fun e => ?_, fun Q hQ hQ0 hQP => ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[e, Ideal.height_bot]`.

Conclude with `zero_ne_one hc`. Assume the negation of the conclusion as `hne haveI : (⊥ : Ideal Γ(X, U)).IsPrime := Ideal.isPrime_bot`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQ0)`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne)`. Rewrite `h1` using `[Ideal.height_bot, zero_add]`.

Rewrite `h2` using `[hc]`. Establish `h4 : (1 : ℕ∞) + 1 ≤ Q.height + 1` using `by gcongr`. Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `h4.trans h2`. Conclude with `absurd h3 (by decide)`.
-/
theorem GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U), Order.coheight z = 1 → (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ → Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  intro X _ U hU z hz h
  haveI : Nonempty U := ⟨⟨z, hz⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  have hc : (hU.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨z, hz⟩).asIdeal
      (X.presheaf.stalk z)
    rw [ringKrullDim_stalk_eq_coheight, h] at this
    exact_mod_cast this.symm
  refine ⟨fun e => ?_, fun Q hQ hQ0 hQP => ?_⟩
  · rw [e, Ideal.height_bot] at hc
    exact zero_ne_one hc
  · by_contra hne
    haveI : (⊥ : Ideal Γ(X, U)).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQ0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne)
    rw [Ideal.height_bot, zero_add] at h1
    rw [hc] at h2
    have h4 : (1 : ℕ∞) + 1 ≤ Q.height + 1 := by gcongr
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans h2
    exact absurd h3 (by decide)
