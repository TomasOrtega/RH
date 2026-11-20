import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEtaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHostStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AutomorphicArithmetic.WeightCongruences.ExistsUnitEqRootOfUnityMulConjPhaseOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.EtaT

/- English proof (translation)
Rewrite using `[← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]`. Use `congr 1`. Use extensionality with `Q`. Simplify using `only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨P, rfl, rfl⟩`. Conclude with `⟨P.isPrime, ⟨rfl⟩⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext h2.over.symm, rfl⟩`.
-/
theorem card_above {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) :
    (aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩

/- English proof (translation)
Establish `: Fact l.Prime` using `⟨hp⟩`. Establish `hPp` using `P.isPrime`. Establish `hPZ : P.asIdeal.LiesOver (Ideal.span {(l : ℤ)})`. Establish `hm : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Use `⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `hP`. Establish `he` using `H.der.eta.2.2 l hl P.asIdeal`. Express the relevant statement in the definitionally equal form `(if (Ideal.primesOver (P.under (𝓞 H.F)).asIdeal (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he`. Rewrite using `[card_above]`.

Assume the negation of the conclusion as `hc`. Rewrite `he` using `[if_neg hc]`. Conclude with `absurd he (by decide)`.
-/
private theorem card_above_of_prime {R : Ranks} (H : Formalism.BasicNotions.Host R) (l : ℕ) (hp : l.Prime) (hl : l ∣ H.condN)
    (P : HeightOneSpectrum (𝓞 H.E)) (hP : ((l : ℕ) : 𝓞 H.E) ∈ P.asIdeal) :
    (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 2 := by
  have : Fact l.Prime := ⟨hp⟩
  have hPp := P.isPrime
  have hPZ : P.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hP
  have he := H.der.eta.2.2 l hl P.asIdeal
  change (if (Ideal.primesOver (P.under (𝓞 H.F)).asIdeal (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
  rw [card_above]
  by_contra hc
  rw [if_neg hc] at he
  exact absurd he (by decide)

/- English proof (translation)
Proceed by induction on `N using induction_on_primes with`. Consider the case `zero => exact absurd rfl hN`. Consider the case `one => exact absurd (P.eq_top_iff_one.2 (by simpa using h)) hP.ne_top`. Consider the case `prime_mul p a hp ih`. Rewrite `h` using `[Nat.cast_mul]`.

Break down `hP.mem_or_mem h with h | h` into its components or cases. Conclude with `⟨p, hp, Dvd.intro _ rfl, h⟩`. Take `⟨l, h1, h2, h3⟩` from `ih (fun h0 => hN (by rw [h0, mul_zero])) h`. Conclude with `⟨l, h1, h2.mul_left _, h3⟩`.
-/
private theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (N : ℕ) (hN : N ≠ 0)
    (h : (N : A) ∈ P) : ∃ l : ℕ, l.Prime ∧ l ∣ N ∧ (l : A) ∈ P := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl hN
  | one => exact absurd (P.eq_top_iff_one.2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨l, h1, h2, h3⟩ := ih (fun h0 => hN (by rw [h0, mul_zero])) h
      exact ⟨l, h1, h2.mul_left _, h3⟩

open Classical in

/- English proof (translation)
Introduce `R H`. Take `⟨c, hc, hcm, hunr, -, -⟩` from `GlobalTheory.Mem.HostCM.host_cm R H`. Take `⟨χ, h1, h2, h3, h4⟩` from `GlobalTheory.T.exists_unramified_resEta_alt H.F H.E c (R.Psi) (embPsi H) hcm hunr (GlobalTheory.T.quadraticChar_product_formula_CM_host R H) (fun _ => 1) (fun _ => odd_one) (fun ζ hζ => by`. Take `⟨δ, hδ, hval, hprod⟩` from `UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one R H R.Psi (Equiv.refl _) ζ hζ`. Use `⟨δ, by rw [hc]; exact hδ, fun P hP => ?_, ?_⟩` and prove the remaining obligations.

Establish `hn : ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal` using `fun hm => by`. Take `⟨l, hl, hlN, hlP⟩` from `exists_prime_mem P.asIdeal P.isPrime H.condN H.condN_ne_zero hm`. Rewrite `hP` using `[card_above_of_prime H l hl hlN P hlP]`. Conclude with `absurd hP (by decide)`. Establish `h0 : ordF P δ = 0` using `by simp [ordF, hval P hn]`.

Rewrite using `[h0]`. Conclude with `Even.zero`. Simplify using `only [zpow_one]`. Conclude with `hprod)`. Conclude with `⟨χ, h1, h2, h3, h4⟩`.
-/
theorem etaT_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  intro R H
  obtain ⟨c, hc, hcm, hunr, -, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unramified_resEta_alt H.F H.E c (R.Psi) (embPsi H) hcm hunr (GlobalTheory.T.quadraticChar_product_formula_CM_host R H)
    (fun _ => 1) (fun _ => odd_one) (fun ζ hζ => by
      obtain ⟨δ, hδ, hval, hprod⟩ := UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one R H R.Psi (Equiv.refl _) ζ hζ
      refine ⟨δ, by rw [hc]; exact hδ, fun P hP => ?_, ?_⟩
      · have hn : ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal := fun hm => by
          obtain ⟨l, hl, hlN, hlP⟩ := exists_prime_mem P.asIdeal P.isPrime H.condN H.condN_ne_zero hm
          rw [card_above_of_prime H l hl hlN P hlP] at hP
          exact absurd hP (by decide)
        have h0 : ordF P δ = 0 := by simp [ordF, hval P hn]
        rw [h0]
        exact Even.zero
      · simp only [zpow_one]
        exact hprod)
  exact ⟨χ, h1, h2, h3, h4⟩

end GlobalTheory.Mem.EtaT
