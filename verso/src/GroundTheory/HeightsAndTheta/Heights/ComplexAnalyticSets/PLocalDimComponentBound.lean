import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimComponentBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem comap_curveLocalRing_strictMono (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by
  refine Monotone.strictMono_of_injective (fun P Q h ↦ Ideal.comap_mono h) ?_
  intro P Q h
  apply PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := I.map
    (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
  apply PrimeSpectrum.localization_comap_injective _ (RingHom.ker (eval q)).primeCompl
  exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem le_comap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by
  intro x hx
  have h0 : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q)))))
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx)
  change algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x ∈ P.asIdeal
  rw [show algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x = 0 from h0]
  exact P.asIdeal.zero_mem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem comap_curveLocalRing_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LocalDimComponentBound.proof : LocalDimComponentBound.Statement := by
  intro n I q hq
  rcases subsingleton_or_nontrivial (curveLocalRing I q) with hO | hO
  · refine ⟨RingHom.ker (eval q), inferInstance, fun x hx ↦ RingHom.mem_ker.2 (hq x hx),
      fun x hx ↦ RingHom.mem_ker.1 hx, ?_⟩
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set f := algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)
  set p := LTSeries.longestOf (PrimeSpectrum (curveLocalRing I q))
  set W := (PrimeSpectrum.comap f p.head).asIdeal with hW
  have hWle : ∀ i, W ≤ (PrimeSpectrum.comap f (p i)).asIdeal := fun i ↦
    Ideal.comap_mono (p.monotone (Fin.zero_le i))
  let p' : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) W) :=
    { length := p.length
      toFun := fun i ↦ ⟨PrimeSpectrum.comap f (p i), hWle i⟩
      step := fun i ↦ comap_curveLocalRing_strictMono I q (p.step i) }
  refine ⟨W, (PrimeSpectrum.comap f p.head).isPrime, le_comap_curveLocalRing I q _,
    fun x hx ↦ RingHom.mem_ker.1 (comap_curveLocalRing_le I q _ hx), ?_⟩
  rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder, ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim p'

end

end GroundTheory.Heights₂.Heights
