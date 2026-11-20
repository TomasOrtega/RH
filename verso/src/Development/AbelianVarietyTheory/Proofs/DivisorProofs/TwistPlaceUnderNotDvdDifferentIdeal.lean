import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistPlDiff

/- English proof (translation)
Establish `hD : (discr D.host.E).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (discr_ne_zero _)`. Establish `hN : D.host.QS * D.host.q * D.host.d ≠ 0` using `D.host.condN_ne_zero`. Use `⟨(discr D.host.E).natAbs, (Nat.dvd_pow_self_iff hD hN).2 fun p hp => ?_⟩` and prove the remaining obligations. Establish `h` using `Nat.mem_primeFactors.1 hp`. Conclude with `Nat.mem_primeFactors.2 ⟨h.1, D.host.der.discr_primes.1 p h.1 (Int.natCast_dvd.2 h.2.1), hN⟩`.
-/
theorem natAbs_discr_dvd_pow (D : D7) : ∃ M : ℕ,
    (discr D.host.E).natAbs ∣ (D.host.QS * D.host.q * D.host.d) ^ M := by
  have hD : (discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  have hN : D.host.QS * D.host.q * D.host.d ≠ 0 := D.host.condN_ne_zero
  refine ⟨(discr D.host.E).natAbs, (Nat.dvd_pow_self_iff hD hN).2 fun p hp => ?_⟩
  have h := Nat.mem_primeFactors.1 hp
  exact Nat.mem_primeFactors.2
    ⟨h.1, D.host.der.discr_primes.1 p h.1 (Int.natCast_dvd.2 h.2.1), hN⟩

/- English proof (translation)
Introduce `D T Lc μ₀ hL t PP hPP hdvd`. Take `⟨h2qdT, -⟩` from `hL.Q_off t PP hPP`. Use `set P := PP.under (𝓞 D.host.F) with hPdef`. Establish `h1 : Ideal.absNorm P.asIdeal ∣ (discr D.host.E).natAbs`. Establish `ha : Ideal.absNorm P.asIdeal ∣ (discr D.host.F).natAbs`.

Rewrite using `[← NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)]`. Conclude with `Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)`. Conclude with `ha.trans (Int.natAbs_dvd_natAbs.2 (NumberField.discr_dvd_discr _ _))`. Take `⟨M, hM⟩` from `natAbs_discr_dvd_pow D`. Establish `hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`.

Use `Ideal.absNorm_mem P.asIdeal` as an intermediate fact. Establish `h' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (Ideal.absNorm P.asIdeal : 𝓞 D.host.F) ∈ PP.asIdeal` using `this`. Simplify using `using h'`. Establish `hpow : (((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)) ^ M ∈ PP.asIdeal`. Take `⟨c, hc⟩` from `h1.trans hM`.

Rewrite using `[← Nat.cast_pow, hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Establish `hx` using `PP.isPrime.mem_of_pow_mem M hpow`. Apply `h2qdT` to reduce the goal to its premises. Rewrite using `[Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hx`.
-/
theorem under_not_dvd_differentIdeal : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T), ∀ PP ∈ Lc.Q t, ¬ (PP.under (𝓞 D.host.F)).asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D T Lc μ₀ hL t PP hPP hdvd
  obtain ⟨h2qdT, -⟩ := hL.Q_off t PP hPP
  set P := PP.under (𝓞 D.host.F) with hPdef

  have h1 : Ideal.absNorm P.asIdeal ∣ (discr D.host.E).natAbs := by
    have ha : Ideal.absNorm P.asIdeal ∣ (discr D.host.F).natAbs := by
      rw [← NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
    exact ha.trans (Int.natAbs_dvd_natAbs.2 (NumberField.discr_dvd_discr _ _))
  obtain ⟨M, hM⟩ := natAbs_discr_dvd_pow D

  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    have h' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (Ideal.absNorm P.asIdeal : 𝓞 D.host.F) ∈ PP.asIdeal := this
    simpa using h'
  have hpow : (((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)) ^ M ∈ PP.asIdeal := by
    obtain ⟨c, hc⟩ := h1.trans hM
    rw [← Nat.cast_pow, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hx := PP.isPrime.mem_of_pow_mem M hpow
  apply h2qdT
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hx

end GlobalTheory.TwistPlDiff
