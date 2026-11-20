import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverConj

/- English proof (translation)
Introduce `a b hab`. Establish `hb : b = Formalism.DivisionValues.cO D.host.E a` using `RingOfIntegers.ext (by rw [hab]; rfl)`. Substitute `hb` using the available equality. Use `show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)`. Prove the components needed by the constructor for the conclusion.

Conclude with `fun h => Ideal.mem_map_of_mem _ h`. Introduce `h`. Rewrite `h` using `[Ideal.mem_map_of_equiv]`. Take `⟨x, hx, hxa⟩` from `h`. Rewrite using `[← (Formalism.DivisionValues.cO D.host.E).injective hxa]` and apply the resulting hypothesis.
-/
theorem isConjugatePlace_conjugateIdealPlace (D : D7) (P : Pl D.host.E) : Formalism.L2.DIV.IsConjPl P (Formalism.DivisionValues.conjPl P) := by
  intro a b hab
  have hb : b = Formalism.DivisionValues.cO D.host.E a := RingOfIntegers.ext (by rw [hab]; rfl)
  subst hb
  show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    rw [Ideal.mem_map_of_equiv] at h
    obtain ⟨x, hx, hxa⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective hxa]

/- English proof (translation)
Introduce `D Pg hPg Q hQ`. Establish `hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hQ`. Take `⟨PP, ⟨hPP, hunder⟩, -⟩` from `hPg.2 _ hv`.

Use `⟨PP, hPP, ?_⟩` and prove the remaining obligations. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h` into its components or cases. Conclude with `Or.inl h`. Use `right`. Introduce `s`.

Establish `hc : Formalism.L2.DIV.IsConjPl PP Q` using `h ▸ isConjugatePlace_conjugateIdealPlace D PP`. Conclude with `(Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm`.
-/
theorem cover : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  intro D Pg hPg Q hQ
  have hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]
    exact hQ
  obtain ⟨PP, ⟨hPP, hunder⟩, -⟩ := hPg.2 _ hv
  refine ⟨PP, hPP, ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h
  · exact Or.inl h
  · right
    intro s
    have hc : Formalism.L2.DIV.IsConjPl PP Q := h ▸ isConjugatePlace_conjugateIdealPlace D PP
    exact (Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm

end GlobalTheory.CoverConj
