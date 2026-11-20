import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open NumberField IsDedekindDomain
open Classical

/- English proof (translation)
Introduce `D T L sc G t l hl w hlw hQ q hq hlq`. Take `⟨P, hP, rfl⟩` from `Finset.mem_image.mp hq`. Establish `hlP : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Establish `h` using `hlq`. Simplify using `only [HeightOneSpectrum.under] at h`.

Establish `: algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ P.asIdeal` using `h`. Simplify using `using this`. Establish `hdvd : l ∣ Ideal.absNorm P.asIdeal`. Establish `h1` using `Ideal.absNorm_dvd_norm_of_mem hlP`. Establish `h2 : ((l : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (l : ℤ)` using `by simp`.

Rewrite `h1` using `[h2, Algebra.norm_algebraMap]`. Establish `h3 : Ideal.absNorm P.asIdeal ∣ l ^ Module.finrank ℤ (𝓞 D.host.E)`. Use `Int.natAbs_dvd_natAbs.mpr h1` as an intermediate fact. Simplify `this` using `[Int.natAbs_pow]`. Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hl).mp h3`.

Establish `hne : Ideal.absNorm P.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `P.isPrime.ne_top`. Break down `k with _ | k` into its components or cases. Rewrite `hk` using `[pow_zero]`.

Conclude with `absurd hk hne`. Rewrite using `[hk]`. Conclude with `dvd_pow_self l (Nat.succ_ne_zero k)`. Establish `hQd : l ∣ GlobalTheory.SqTop.Qn G t` using `dvd_trans hdvd (Finset.dvd_prod_of_mem _ hP)`. Take `⟨k, hk⟩` from `hQd`.

Apply `hQ` to reduce the goal to its premises. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `w.asIdeal.mul_mem_right _ hlw`.
-/
theorem GlobalTheory.twPl_under_not_mem_prime : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL}, (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal → ∀ q ∈ ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal := by
  intro D T L sc G t l hl w hlw hQ q hq hlq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
  have hlP : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h := hlq
    simp only [HeightOneSpectrum.under] at h
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ P.asIdeal := h
    simpa using this
  have hdvd : l ∣ Ideal.absNorm P.asIdeal := by
    have h1 := Ideal.absNorm_dvd_norm_of_mem hlP
    have h2 : ((l : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (l : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have h3 : Ideal.absNorm P.asIdeal ∣ l ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      simpa [Int.natAbs_pow] using this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp h3
    have hne : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact P.isPrime.ne_top
    rcases k with _ | k
    · rw [pow_zero] at hk; exact absurd hk hne
    · rw [hk]; exact dvd_pow_self l (Nat.succ_ne_zero k)
  have hQd : l ∣ GlobalTheory.SqTop.Qn G t :=
    dvd_trans hdvd (Finset.dvd_prod_of_mem _ hP)
  obtain ⟨k, hk⟩ := hQd
  apply hQ
  rw [hk, Nat.cast_mul]
  exact w.asIdeal.mul_mem_right _ hlw
