import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Introduce `n e J hJ he q hq`. Use `hJ` as an intermediate fact. Use `set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)`. Establish `hJM : J ≤ M` using `fun f hf => RingHom.mem_ker.mpr (hq f hf)`. Set `m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J)` to `M.map (Ideal.Quotient.mk J)`.

Establish `hm : m.IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJM)`. Establish `hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl = m.primeCompl`. Use extensionality with `x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, hzy⟩`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J y ∉ m`. Rewrite using `[← hzy]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J z ∉ M.map (Ideal.Quotient.mk J)`. Rewrite using `[Ideal.mem_quotient_iff_mem hJM]`.

Conclude with `hz`. Introduce `h`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J y ∉ M.map (Ideal.Quotient.mk J) at h`. Rewrite `h` using `[Ideal.mem_quotient_iff_mem hJM]`. Conclude with `⟨y, h, rfl⟩`.

Establish `: m.IsPrime` using `hm.isPrime`. Establish `: IsLocalization.AtPrime (localRingAt J q) m`. Unfold `IsLocalization.AtPrime`. Rewrite using `[← hsub]`. Unfold `localRingAt`.

Use `infer_instance`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q), NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]`.
-/
theorem LocalDimDomain.proof : LocalDimDomain.Statement := by
  intro n e J hJ he q hq
  have := hJ
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hJM : J ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := M.map (Ideal.Quotient.mk J)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk J y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk J z ∉ M.map (Ideal.Quotient.mk J)
      rw [Ideal.mem_quotient_iff_mem hJM]
      exact hz
    · intro h
      change Ideal.Quotient.mk J y ∉ M.map (Ideal.Quotient.mk J) at h
      rw [Ideal.mem_quotient_iff_mem hJM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt J q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q),
    NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]

end GroundTheory.Heights₂.Heights
