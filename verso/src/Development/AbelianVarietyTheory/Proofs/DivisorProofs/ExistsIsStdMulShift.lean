import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRangeOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMapIntegrableDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeIntegralNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GramOfIsWittBasis
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDoubleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticHermitianSkew
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow
namespace GlobalTheory.StdRescale

/- English proof (translation)
Introduce `F _ _ hF ψ h`. Use `haveI := hF`. Take `⟨a₀, ha₀, hinf⟩` from `GlobalTheory.AdeleCharConductor.exists_scaling h`. Establish `him : ∀ (w : InfinitePlace F) (x : F), (w.embedding x).im = 0` using `fun w x => by`. Use `congrArg Complex.im (GlobalTheory.AdeleCharConductor.embedding_re w x)` as an intermediate fact.

Simplify using `using this.symm`. Establish `hkey : ∀ w : InfinitePlace F, (w.embedding a₀).re * (w.embedding (-a₀⁻¹)).re = -1` using `fun w => by`. Use `congrArg Complex.re (show w.embedding (a₀ * -a₀⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ ha₀, map_neg, map_one])` as an intermediate fact. Rewrite `this` using `[map_mul, Complex.mul_re, him, him, mul_zero, sub_zero]`. Simplify using `using this`.

Use `⟨-a₀⁻¹, neg_ne_zero.2 (inv_ne_zero ha₀), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `h.1.comp (continuous_const.mul continuous_id)`. Introduce `x`. Rewrite using `[AddChar.mulShift_apply, ← map_mul]`. Conclude with `h.2.2.1 _`.

Introduce `b hb`. Establish `hu : evI F (pairA F 0 1) = 0` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`. Establish `hb2 : b.2 = 0`. Establish `h0` using `congrArg Prod.snd (hb (pairA F 0 1) hu)`.

Express the relevant statement in the definitionally equal form `(1 : Af F) * b.2 = 0 at h0`. Rewrite `h0` using `[one_mul]`. Then use the resulting hypothesis. Establish `e1 : algebraMap F (AF F) (-a₀⁻¹) * b = pairA F (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) 0`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap F (AF F) (-a₀⁻¹)).2 * b.2 = 0`.

Rewrite using `[hb2, mul_zero]`. Establish `hterm : ∀ w : InfinitePlace F, (w.embedding a₀).re * (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w)).re = -(InfinitePlace.Completion.extensionEmbedding w (b.1 w)).re` using `fun w => by`. Rewrite using `[show (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w = algebraMap F (Ainf F) (-a₀⁻¹) w * b.1 w from rfl, map_mul, GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap, Complex.mul_re, him, zero_mul, sub_zero, ← mul_assoc, hkey, neg_one_mul]`. Rewrite using `[AddChar.mulShift_apply, e1]`. Use `show psiInf F ψ _ = _`.

Rewrite using `[hinf, GlobalTheory.WrongSignPair.trace_evI]`. Simplify using `only [hterm, Finset.sum_neg_distrib]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem exists_isStd_mulShift : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∃ a : F, a ≠ 0 ∧ IsStd (ψ.mulShift (algebraMap F (AF F) a)) := by
  intro F _ _ hF ψ h
  haveI := hF
  obtain ⟨a₀, ha₀, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling h
  have him : ∀ (w : InfinitePlace F) (x : F), (w.embedding x).im = 0 := fun w x => by
    have := congrArg Complex.im (GlobalTheory.AdeleCharConductor.embedding_re w x)
    simpa using this.symm
  have hkey : ∀ w : InfinitePlace F, (w.embedding a₀).re * (w.embedding (-a₀⁻¹)).re = -1 := fun w => by
    have := congrArg Complex.re
      (show w.embedding (a₀ * -a₀⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ ha₀, map_neg, map_one])
    rw [map_mul, Complex.mul_re, him, him, mul_zero, sub_zero] at this
    simpa using this
  refine ⟨-a₀⁻¹, neg_ne_zero.2 (inv_ne_zero ha₀), ?_, ?_, ?_⟩
  · exact h.1.comp (continuous_const.mul continuous_id)
  · intro x
    rw [AddChar.mulShift_apply, ← map_mul]
    exact h.2.2.1 _
  · intro b hb
    have hu : evI F (pairA F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have hb2 : b.2 = 0 := by
      have h0 := congrArg Prod.snd (hb (pairA F 0 1) hu)
      change (1 : Af F) * b.2 = 0 at h0
      rwa [one_mul] at h0
    have e1 : algebraMap F (AF F) (-a₀⁻¹) * b = pairA F (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) 0 := by
      refine Prod.ext rfl ?_
      change (algebraMap F (AF F) (-a₀⁻¹)).2 * b.2 = 0
      rw [hb2, mul_zero]
    have hterm : ∀ w : InfinitePlace F, (w.embedding a₀).re *
        (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w)).re =
        -(InfinitePlace.Completion.extensionEmbedding w (b.1 w)).re := fun w => by
      rw [show (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w = algebraMap F (Ainf F) (-a₀⁻¹) w * b.1 w from rfl, map_mul, GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap, Complex.mul_re, him,
        zero_mul, sub_zero, ← mul_assoc, hkey, neg_one_mul]
    rw [AddChar.mulShift_apply, e1]
    show psiInf F ψ _ = _
    rw [hinf, GlobalTheory.WrongSignPair.trace_evI]
    simp only [hterm, Finset.sum_neg_distrib]
    push_cast
    ring_nf

end GlobalTheory.StdRescale
