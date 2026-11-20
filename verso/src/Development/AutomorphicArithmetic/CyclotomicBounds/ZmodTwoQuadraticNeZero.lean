import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Development.AutomorphicArithmetic.PrimeDiscriminants.SmallRam
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

namespace UpperTheory.Small

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Introduce `h` and use `hs (Nat.mem_primeFactors.2 ⟨hl, h, H.QS_pos.ne'⟩)`.
-/
theorem not_dvd_QS {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) : ¬ l ∣ H.QS := fun h =>
  hs (Nat.mem_primeFactors.2 ⟨hl, h, H.QS_pos.ne'⟩)

/- English proof (translation)
Introduce `h`. Break down `(Nat.Prime.dvd_mul hl).1 h with h1 | h1` into its components or cases. Break down `(Nat.Prime.dvd_mul hl).1 h1 with h2 | h2` into its components or cases. Conclude with `not_dvd_QS H hl hs h2`. Conclude with `hq ((Nat.prime_dvd_prime_iff_eq hl H.hyp.1).1 h2)`.

Conclude with `hd ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).1 h1)`.
-/
theorem not_dvd_condN {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) (hd : l ≠ H.d) : ¬ l ∣ H.condN := by
  intro h
  rcases (Nat.Prime.dvd_mul hl).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hl).1 h1 with h2 | h2
    · exact not_dvd_QS H hl hs h2
    · exact hq ((Nat.prime_dvd_prime_iff_eq hl H.hyp.1).1 h2)
  · exact hd ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).1 h1)

/- English proof (translation)
Establish `hq` using `H.hyp.1`. Establish `hd` using `H.hyp.2.1`. Establish `h8` using `H.hyp.2.2.1`. Establish `h16` using `H.hyp.2.2.2.1`. Establish `e : H.condN.factorization l = H.QS.factorization l + H.q.factorization l + H.d.factorization l` using `by show (H.QS * H.q * H.d).factorization l = _`.

Rewrite using `[Nat.factorization_mul (mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero, Nat.factorization_mul H.QS_pos.ne' hq.ne_zero]`. Both sides reduce to the same expression. Rewrite using `[e, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]`. Distinguish the cases in `h1 : H.q = l`. Establish `hs` using `factorization_eq_zero H (h1 ▸ q_not_mem H)`.

Establish `h2 : H.d ≠ l` using `by omega`. Rewrite using `[if_pos h1, if_neg h2, hs]`. Conclude with `⟨by simp, fun h => by omega⟩`. Distinguish the cases in `h2 : H.d = l`. Establish `hs` using `factorization_eq_zero H (h2 ▸ d_not_mem H)`.

Rewrite using `[if_neg h1, if_pos h2, hs]`. Conclude with `⟨by simp, fun h => by omega⟩`. Rewrite using `[if_neg h1, if_neg h2]`. Conclude with `⟨by simp, fun _ => by simp⟩`.
-/
theorem factorization_condN_le {l : ℕ} (hl : l.Prime) :
    H.condN.factorization l ≤ max 1 (H.QS.factorization l) ∧ (l = 2 → H.condN.factorization l ≤ H.QS.factorization l) := by
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have h8 := H.hyp.2.2.1
  have h16 := H.hyp.2.2.2.1
  have e : H.condN.factorization l = H.QS.factorization l + H.q.factorization l + H.d.factorization l := by
    show (H.QS * H.q * H.d).factorization l = _
    rw [Nat.factorization_mul (mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero,
      Nat.factorization_mul H.QS_pos.ne' hq.ne_zero]
    rfl
  rw [e, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h1 : H.q = l
  · have hs := factorization_eq_zero H (h1 ▸ q_not_mem H)
    have h2 : H.d ≠ l := by omega
    rw [if_pos h1, if_neg h2, hs]
    exact ⟨by simp, fun h => by omega⟩
  · by_cases h2 : H.d = l
    · have hs := factorization_eq_zero H (h2 ▸ d_not_mem H)
      rw [if_neg h1, if_pos h2, hs]
      exact ⟨by simp, fun h => by omega⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨by simp, fun _ => by simp⟩

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hN` using `H.toHostRaw.condN_ne_zero`. Use `H.toHostRaw.image_mem_of_roots J (MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}).toSubfield (fun y hy => ?_) x` and prove the remaining obligations. Use `set a := l ^ H.condN.factorization l with ha`. Use `set b := H.condN / a with hb`.

Establish `hab : a * b = H.condN` using `Nat.ordProj_mul_ordCompl_eq_self _ _`. Establish `hco : Nat.Coprime a b` using `(Nat.coprime_ordCompl hl hN).pow_left _`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[zero_pow hN]`.

Conclude with `zero_ne_one hy`. Establish `hbez` using `Nat.gcd_eq_gcd_ab a b`. Rewrite `hbez` using `[hco.gcd_eq_one]`. Establish `e : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b)`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hy0, ← hbez]`.

Simplify using the standard rewrite rules. Establish `h1 : y ^ a ∈ MaximalUnramifiedExtension l` using `IntermediateField.subset_adjoin _ _ ⟨b, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl hl hN, by rw [← pow_mul, hab, hy]⟩`. Establish `h2 : y ^ b ∈ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}`. Use `IntermediateField.subset_adjoin _ _ ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `pow_dvd_pow l hs`.

Use `show (y ^ b) ^ (l ^ s) = 1`. Rewrite using `[hc, ← ha, ← pow_mul, ← mul_assoc, mul_comm b a, hab, pow_mul, hy, one_pow]`. Use `show y ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}`. Rewrite using `[e]`. Conclude with `mul_mem (zpow_mem ((le_sup_left : MaximalUnramifiedExtension l ≤ _) h1) _) (zpow_mem ((le_sup_right : IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} ≤ _) h2) _)`.
-/
theorem image_mem_Kur_sup {l : ℕ} [Fact l.Prime] (J : H.E →+* Om l) {s : ℕ} (hs : H.condN.factorization l ≤ s) (x : H.E) :
    J x ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
  have hl : l.Prime := Fact.out
  have hN := H.toHostRaw.condN_ne_zero
  refine H.toHostRaw.image_mem_of_roots J
    (MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}).toSubfield (fun y hy => ?_) x
  set a := l ^ H.condN.factorization l with ha
  set b := H.condN / a with hb
  have hab : a * b = H.condN := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hco : Nat.Coprime a b := (Nat.coprime_ordCompl hl hN).pow_left _
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hy
    exact zero_ne_one hy
  have hbez := Nat.gcd_eq_gcd_ab a b
  rw [hco.gcd_eq_one] at hbez
  have e : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hy0, ← hbez]
    simp
  have h1 : y ^ a ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _
    ⟨b, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl hl hN, by rw [← pow_mul, hab, hy]⟩
  have h2 : y ^ b ∈ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
    refine IntermediateField.subset_adjoin _ _ ?_
    obtain ⟨c, hc⟩ := pow_dvd_pow l hs
    show (y ^ b) ^ (l ^ s) = 1
    rw [hc, ← ha, ← pow_mul, ← mul_assoc, mul_comm b a, hab, pow_mul, hy, one_pow]
  show y ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}
  rw [e]
  exact mul_mem (zpow_mem ((le_sup_left : MaximalUnramifiedExtension l ≤ _) h1) _)
    (zpow_mem ((le_sup_right : IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} ≤ _) h2) _)

/- English proof (translation)
Introduce `hs`. Take `⟨P, hPp, hP0⟩` from `P`. Establish `h2` using `H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hl (Nat.dvd_of_mem_primeFactors hs) P hP`. Establish `he' : P.ramificationIdx ℤ = 1` using `he`. Establish `hmax : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible`.

Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 H.E)}`. Rewrite using `[Ideal.map_span]`. Simplify using the standard rewrite rules. Establish `hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) ≤ P`. Rewrite using `[hmap, Ideal.span_le]`.

Simplify using `using hP`. Establish `: P.LiesOver (Ideal.span {(l : ℤ)})` using `⟨hmax.eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩`. Establish `hb : Ideal.span {(l : ℤ)} ≠ ⊥` using `by simpa using hl.ne_zero`. Rewrite `he'` using `[← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) P hb]`. Use `(Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'` and prove the remaining obligations.

Rewrite using `[hmap, Ideal.span_le]`. Simplify using `using h2`.
-/
theorem not_mem_of_ramIdx_one {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 H.E)) (hP : (l : 𝓞 H.E) ∈ P.asIdeal)
    (he : P.asIdeal.ramificationIdx ℤ = 1) : l ∉ H.small := by
  intro hs
  obtain ⟨P, hPp, hP0⟩ := P
  have h2 := H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hl (Nat.dvd_of_mem_primeFactors hs) P hP
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 H.E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hP
  have : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) P hb] at he'
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem zmod_two_quadratic_ne_zero : ∀ v : ZMod 2, v ^ 2 - v + 1 ≠ 0 := by decide

/- English proof (translation)
Introduce `hc`. Establish `h8` using `H.hyp.2.2.1`. Take `⟨k, hk⟩ : ∃ k, H.q = 8 * k + 3` from `⟨H.q / 8, by omega⟩`. Establish `hx : ((1 + H.sqq) / 2) ^ 2 - (1 + H.sqq) / 2 + ((2 * k + 1 : ℕ) : H.E) = 0`. Establish `h` using `H.sqq_sq`.

Rewrite `h` using `[hk]`. Move the coercions through the operations in `at h ⊢`. Take the linear combination `(1 / 4 : H.E) * h`. Establish `hi : IsIntegral ℤ ((1 + H.sqq) / 2)`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 1 : ℕ) : ℤ), by monicity!, ?_⟩` and prove the remaining obligations.

Simplify using `using hx`. Set `z : 𝓞 H.E` to `⟨_, hi⟩`. Establish `hz : z ^ 2 - z + ((2 * k + 1 : ℕ) : 𝓞 H.E) = 0`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [map_add, map_sub, map_pow, map_natCast, map_zero]`.

Conclude with `hx`. Use `haveI := P.isPrime`. Use `haveI : Finite (𝓞 H.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by omega)`. Use `letI := Fintype.ofFinite (𝓞 H.E ⧸ P.asIdeal)`. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`.

Set `e` to `ZMod.ringEquivOfPrime (𝓞 H.E ⧸ P.asIdeal) Nat.prime_two (Nat.card_eq_fintype_card.symm.trans hc)`. Establish `h` using `congrArg (fun t => e.symm (Ideal.Quotient.mk P.asIdeal t)) hz`. Simplify using `only [map_add, map_sub, map_pow, map_natCast, map_zero] at h`. Generalize the expression as in `e.symm (Ideal.Quotient.mk P.asIdeal z) = u at h`. Move the coercions through the operations in `at h`.

Establish `h2 : (2 : ZMod 2) = 0` using `rfl`. Rewrite `h` using `[h2, zero_mul, zero_add]`. Conclude with `zmod_two_quadratic_ne_zero u h`.
-/
theorem card_quot_ne_two (P : HeightOneSpectrum (𝓞 H.E)) : Nat.card (𝓞 H.E ⧸ P.asIdeal) ≠ 2 := by
  intro hc
  have h8 := H.hyp.2.2.1
  obtain ⟨k, hk⟩ : ∃ k, H.q = 8 * k + 3 := ⟨H.q / 8, by omega⟩
  have hx : ((1 + H.sqq) / 2) ^ 2 - (1 + H.sqq) / 2 + ((2 * k + 1 : ℕ) : H.E) = 0 := by
    have h := H.sqq_sq
    rw [hk] at h
    push_cast at h ⊢
    linear_combination (1 / 4 : H.E) * h
  have hi : IsIntegral ℤ ((1 + H.sqq) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 1 : ℕ) : ℤ), by monicity!, ?_⟩
    simpa using hx
  let z : 𝓞 H.E := ⟨_, hi⟩
  have hz : z ^ 2 - z + ((2 * k + 1 : ℕ) : 𝓞 H.E) = 0 := by
    apply RingOfIntegers.ext
    simp only [map_add, map_sub, map_pow, map_natCast, map_zero]
    exact hx
  haveI := P.isPrime
  haveI : Finite (𝓞 H.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (𝓞 H.E ⧸ P.asIdeal)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := ZMod.ringEquivOfPrime (𝓞 H.E ⧸ P.asIdeal) Nat.prime_two (Nat.card_eq_fintype_card.symm.trans hc)
  have h := congrArg (fun t => e.symm (Ideal.Quotient.mk P.asIdeal t)) hz
  simp only [map_add, map_sub, map_pow, map_natCast, map_zero] at h
  generalize e.symm (Ideal.Quotient.mk P.asIdeal z) = u at h
  push_cast at h
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, zero_add] at h
  exact zmod_two_quadratic_ne_zero u h

end UpperTheory.Small
