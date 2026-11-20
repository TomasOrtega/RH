import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Development.AutomorphicArithmetic.PrimeDiscriminants.SmallRam

open NumberField IsDedekindDomain Ideal

noncomputable section

namespace Formalism.HC

/- English proof (translation)
Assume the negation of the conclusion as `hd`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hmax : (span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible`. Take `⟨P, hPm, hlo⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})`. Establish `hP` using `hPm.isPrime`.

Establish `hb : span {(p : ℤ)} ≠ ⊥` using `by simpa using hp.ne_zero`. Establish `hv : (p : 𝓞 E) ∈ P` using `by simpa using (Ideal.liesOver_span_iff hP.ne_top hpz).1 hlo`. Establish `hun` using `(not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd P hP (by simpa using hv)`. Establish `hu : P.under ℤ = span {(p : ℤ)}` using `hlo.over.symm`. Establish `: Finite (ℤ ⧸ P.under ℤ)` using `Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)`.

Establish `: (P.under ℤ).IsMaximal` using `hu ▸ hmax`. Establish `: Finite (P.under ℤ).ResidueField` using `inferInstance`. Establish `he : P.ramificationIdx ℤ = 1` using `Ideal.ramificationIdx_eq_one_iff.2 hun`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) = span {(p : 𝓞 E)}`. Rewrite using `[Ideal.map_span]`.

Simplify using the standard rewrite rules. Establish `hle : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) ≤ P`. Rewrite using `[hmap, Ideal.span_le]`. Simplify using `using hv`. Rewrite `he` using `[← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hb]`.

Use `(Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he` and prove the remaining obligations. Rewrite using `[hmap, Ideal.span_le]`. Simplify using `using h P hP hv`.
-/
theorem dvd_discr_of_mem_sq (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → (p : 𝓞 E) ∈ P ^ 2) : (p : ℤ) ∣ discr E := by
  by_contra hd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  obtain ⟨P, hPm, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})
  have hP := hPm.isPrime
  have hb : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hv : (p : 𝓞 E) ∈ P := by simpa using (Ideal.liesOver_span_iff hP.ne_top hpz).1 hlo
  have hun := (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd P hP (by simpa using hv)
  have hu : P.under ℤ = span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (P.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (P.under ℤ).ResidueField := inferInstance
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) = span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h P hP hv

/- English proof (translation)
Establish `hi : IsIntegral ℤ a` using `IsIntegral.of_pow two_pos (ha ▸ (isIntegral_natCast p).neg)`. Set `b : 𝓞 E` to `⟨a, hi⟩`. Establish `hb : b ^ 2 = -(p : 𝓞 E)` using `RingOfIntegers.ext (by`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]`. Conclude with `ha)`.

Use `dvd_discr_of_mem_sq E hp fun P hP hv => ?_` and prove the remaining obligations. Establish `h1 : b ∈ P` using `hP.mem_of_pow_mem 2 (hb ▸ P.neg_mem hv)`. Establish `h2` using `(P ^ 2).neg_mem (Ideal.pow_mem_pow h1 2)`. Rewrite `h2` using `[hb, neg_neg]`. Then use the resulting hypothesis.
-/
theorem dvd_discr_of_sqrt (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {a : E} (ha : a ^ 2 = -(p : E)) :
    (p : ℤ) ∣ discr E := by
  have hi : IsIntegral ℤ a := IsIntegral.of_pow two_pos (ha ▸ (isIntegral_natCast p).neg)
  let b : 𝓞 E := ⟨a, hi⟩
  have hb : b ^ 2 = -(p : 𝓞 E) := RingOfIntegers.ext (by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]; exact ha)
  refine dvd_discr_of_mem_sq E hp fun P hP hv => ?_
  have h1 : b ∈ P := hP.mem_of_pow_mem 2 (hb ▸ P.neg_mem hv)
  have h2 := (P ^ 2).neg_mem (Ideal.pow_mem_pow h1 2)
  rwa [hb, neg_neg] at h2

/- English proof (translation)
The claim follows from `dvd_discr_of_mem_sq H.E hl fun P _ hv => H.mem_sq_of_dvd_QS hE hl hd P hv`.
-/
theorem HostAx.dvd_discr_of_dvd_QS {φ : Frame} (H : HostAx φ) (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) :
    (l : ℤ) ∣ discr H.E :=
  dvd_discr_of_mem_sq H.E hl fun P _ hv => H.mem_sq_of_dvd_QS hE hl hd P hv

end Formalism.HC

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
The claim follows from `Formalism.HC.dvd_discr_of_sqrt H.E H.q_prime H.sqq_sq`.
-/
theorem q_dvd_discr : (H.q : ℤ) ∣ discr H.E := Formalism.HC.dvd_discr_of_sqrt H.E H.q_prime H.sqq_sq

/- English proof (translation)
Use `⟨H.der.discr_primes.1 p hp, fun h => ?_⟩` and prove the remaining obligations. Break down `(H.dvd_condN_iff hp).1 h with h | rfl | rfl` into its components or cases. Conclude with `H.toHostAx.dvd_discr_of_dvd_QS H.QS_exact hp h`. Conclude with `H.q_dvd_discr`. Conclude with `H.der.discr_primes.2.2`.
-/
theorem dvd_discr_iff_dvd_condN {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ discr H.E ↔ p ∣ H.condN := by
  refine ⟨H.der.discr_primes.1 p hp, fun h => ?_⟩
  rcases (H.dvd_condN_iff hp).1 h with h | rfl | rfl
  · exact H.toHostAx.dvd_discr_of_dvd_QS H.QS_exact hp h
  · exact H.q_dvd_discr
  · exact H.der.discr_primes.2.2

/- English proof (translation)
The claim follows from `Int.natCast_dvd.symm.trans (H.dvd_discr_iff_dvd_condN hp)`.
-/
theorem dvd_natAbs_discr_iff {p : ℕ} (hp : p.Prime) : p ∣ (discr H.E).natAbs ↔ p ∣ H.condN :=
  Int.natCast_dvd.symm.trans (H.dvd_discr_iff_dvd_condN hp)

end Formalism.BasicNotions.Host

end
