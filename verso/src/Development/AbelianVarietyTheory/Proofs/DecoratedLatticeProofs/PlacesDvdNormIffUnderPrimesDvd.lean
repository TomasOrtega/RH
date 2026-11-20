import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.Columns.BaseLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormPlaces

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem places_dvd_iff (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ)
    (hc : (π' : D.host.E) = star (π : D.host.E)) (hT : π * π' = (T : 𝓞 D.host.E)) (hπ : π ≠ 0)
    (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  have hmap : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) = (T : 𝓞 D.host.E) := map_natCast _ _
  constructor
  · intro hx
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
    have hker : RingHom.ker (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ x.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le
    haveI := x.isPrime
    obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal (𝓞 D.host.E))
      (by rw [← RingHom.ker_eq_comap_bot]; exact hker)
    have hQb : Q ≠ ⊥ := by
      rintro rfl
      apply x.ne_bot
      rw [← hQ, Ideal.comap_bot_of_injective _ hinj]
    let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQp, hQb⟩
    have hw : w.under (𝓞 D.host.F) = x := HeightOneSpectrum.ext hQ
    have hTw : π * π' ∈ w.asIdeal := by
      rw [hT, ← hmap]
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) ∈ Q
      rw [← Ideal.mem_comap, hQ]; exact hx
    rcases w.isPrime.mem_or_mem hTw with h | h
    · exact ⟨w, (Formalism.L2.Col.mem_divs hπ w).2 h, hw⟩
    · refine ⟨GlobalTheory.IdemSupport.cP w, (Formalism.L2.Col.mem_divs hπ _).2 ?_, (GlobalTheory.IdemSupport.under_cP w).trans hw⟩
      rw [GlobalTheory.IdemSupport.mem_cP]
      have : GlobalTheory.IdemSupport.cO D π = π' := by
        apply RingOfIntegers.ext
        rw [GlobalTheory.IdemSupport.cO_coe, hc]
      rw [this]; exact h
  · rintro ⟨w, hw, rfl⟩
    have h1 : π ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hπ w).1 hw
    have h2 : (T : 𝓞 D.host.E) ∈ w.asIdeal := hT ▸ w.asIdeal.mul_mem_right π' h1
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (T : 𝓞 D.host.F) ∈ w.asIdeal
    rw [hmap]; exact h2

end GlobalTheory.NormPlaces
