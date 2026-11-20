import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
private lemma crtPrimes (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (f : ℕ → ℤ) :
    ∃ R : ℤ, ∀ q ∈ T, (q : ℤ) ∣ R - f q := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T ha ih =>
    obtain ⟨R₀, hR₀⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    have hap : a.Prime := hT a (Finset.mem_insert_self a T)
    have hcop : IsCoprime (a : ℤ) (∏ q ∈ T, (q : ℤ)) := by
      refine IsCoprime.prod_right (fun q hq => ?_)
      have hqp : q.Prime := hT q (Finset.mem_insert_of_mem hq)
      have hne : a ≠ q := fun h => ha (h ▸ hq)
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hap hqp).mpr hne)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨R₀ + v * (∏ q ∈ T, (q : ℤ)) * (f a - R₀), fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · refine ⟨-u * (f q - R₀), ?_⟩
      linear_combination (f q - R₀) * huv
    · have h1 : (q : ℤ) ∣ ∏ q ∈ T, (q : ℤ) := Finset.dvd_prod_of_mem (fun q : ℕ => (q : ℤ)) hq'
      obtain ⟨k, hk⟩ := h1
      obtain ⟨l, hl⟩ := hR₀ q hq'
      refine ⟨l + v * k * (f a - R₀), ?_⟩
      rw [hk]
      linear_combination hl

/- English proof (translation)
Proceed by induction. Treat this case separately. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private lemma primeDvdOfMem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (M : ℕ) (hM : 0 < M)
    (h : (M : A) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q : A) ∈ P := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases h1 : M = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
    · have hq : M.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd M
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm; omega
        · exact h0
      have hlt : m < M := by
        have := hq.two_le
        rw [hm]
        nlinarith
      have hmem : ((M.minFac : A)) * (m : A) ∈ P := by
        have : (M : A) = ((M.minFac : A)) * (m : A) := by
          conv_lhs => rw [hm]
          push_cast
          rfl
        rwa [this] at h
      rcases hP.mem_or_mem hmem with h2 | h2
      · exact ⟨M.minFac, hq, Nat.minFac_dvd M, h2⟩
      · obtain ⟨q, hq', hqm, hqP⟩ := ih m hlt hm0 h2
        exact ⟨q, hq', hqm.trans ⟨M.minFac, by rw [mul_comm]; exact hm⟩, hqP⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Take a linear combination of the given relations to obtain the conclusion.
-/
private lemma localInv (q : ℕ) (hq : q.Prime) (tr nm r : ℤ) (hD : ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (q : ℤ) ∣ r ^ 2 - tr * r + nm) : ∃ s : ℤ, (q : ℤ) ∣ s * (tr - 2 * r) - 1 := by
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnd : ¬ (q : ℤ) ∣ tr - 2 * r := by
    intro h
    apply hD
    have h2 : (q : ℤ) ∣ (tr - 2 * r) ^ 2 - 4 * (r ^ 2 - tr * r + nm) :=
      dvd_sub (dvd_pow h two_ne_zero) (Dvd.dvd.mul_left hr 4)
    have h3 : (tr - 2 * r) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [h3] at h2
  have hco : IsCoprime (q : ℤ) (tr - 2 * r) := (Prime.coprime_iff_not_dvd hpr).mpr hnd
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨b, -a, ?_⟩
  linear_combination hab

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Move the embeddings inside the algebraic operations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.W2.Seed.pIdemEx :
    IdemEx := by
  intro E _ _ bar ω tr nm _ hsum hprod M hM hloc
  have hex : ∀ q : ℕ, q.Prime → q ∣ M → ∃ r s : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm ∧
      (q : ℤ) ∣ s * (tr - 2 * r) - 1 := by
    intro q hq hqM
    obtain ⟨hD, r, hr⟩ := hloc q hq hqM
    obtain ⟨s, hs⟩ := localInv q hq tr nm r hD hr
    exact ⟨r, s, hr, hs⟩
  choose! r s hr hs using hex
  have hT : ∀ q ∈ M.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  obtain ⟨R, hR⟩ := crtPrimes M.primeFactors hT r
  obtain ⟨S, hS⟩ := crtPrimes M.primeFactors hT s
  have hbar : bar ω = (tr : 𝓞 E) - ω := by rw [← hsum]; ring
  refine ⟨(S : 𝓞 E) * (ω - (R : 𝓞 E)), fun P hP hMP => ?_⟩
  obtain ⟨q, hq, hqM, hqP⟩ := primeDvdOfMem P hP.isPrime M hM hMP
  have hqf : q ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqM, hM.ne'⟩
  have castMem : ∀ z : ℤ, (q : ℤ) ∣ z → (z : 𝓞 E) ∈ P := by
    rintro z ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hqP
  obtain ⟨a, ha⟩ := hR q hqf
  obtain ⟨b, hb⟩ := hS q hqf
  obtain ⟨c, hc⟩ := hr q hq hqM
  obtain ⟨e, he⟩ := hs q hq hqM
  have h1 : (q : ℤ) ∣ S * (tr - 2 * R) - 1 := by
    refine ⟨b * (tr - 2 * R) + e - 2 * s q * a, ?_⟩
    linear_combination (tr - 2 * R) * hb + he - 2 * s q * ha
  have h2 : (q : ℤ) ∣ R ^ 2 - tr * R + nm := by
    refine ⟨a * (R + r q - tr) + c, ?_⟩
    linear_combination (R + r q - tr) * ha + hc
  have hbe : bar ((S : 𝓞 E) * (ω - (R : 𝓞 E))) = (S : 𝓞 E) * ((tr : 𝓞 E) - ω - (R : 𝓞 E)) := by
    rw [map_mul, map_sub, map_intCast, map_intCast, hbar]
  rw [hbe]
  constructor
  · have := castMem _ h1
    push_cast at this
    convert this using 1
    ring
  · have := Ideal.mul_mem_left P ((S : 𝓞 E) ^ 2) (castMem _ h2)
    push_cast at this
    convert this using 1
    have hp : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbar]; exact hprod
    linear_combination (S : 𝓞 E) ^ 2 * hp
