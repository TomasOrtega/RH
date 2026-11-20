import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr

open NumberField IsDedekindDomain

namespace UpperTheory.Ram

/- English proof (translation)
Establish `hint : IsIntegral ℤ a`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[ha]`. Establish `e : -(p : E) = algebraMap ℤ E (-(p : ℤ))` using `by simp`. Rewrite using `[e]`.

Conclude with `isIntegral_algebraMap`. Use `set b : 𝓞 E := ⟨a, hint⟩ with hb`. Establish `hb2 : b ^ 2 = -(p : 𝓞 E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `push_cast`.

Conclude with `ha`. Establish `hbP : b ∈ P`. Apply `hP.mem_of_pow_mem 2` to reduce the goal to its premises. Rewrite using `[hb2]`. Conclude with `P.neg_mem hv`.

Establish `hsq : b ^ 2 ∈ P ^ 2` using `Ideal.pow_mem_pow hbP 2`. Rewrite `hsq` using `[hb2]`. Simplify using `using (P ^ 2).neg_mem hsq`.
-/
private theorem mem_sq_of_sqrt {E : Type} [Field E] [NumberField E] {p : ℕ} {a : E} (ha : a ^ 2 = -(p : E))
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hv : (p : 𝓞 E) ∈ P) : (p : 𝓞 E) ∈ P ^ 2 := by
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    have e : -(p : E) = algebraMap ℤ E (-(p : ℤ)) := by simp
    rw [e]
    exact isIntegral_algebraMap
  set b : 𝓞 E := ⟨a, hint⟩ with hb
  have hb2 : b ^ 2 = -(p : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact ha
  have hbP : b ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hb2]
    exact P.neg_mem hv
  have hsq : b ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hbP 2
  rw [hb2] at hsq
  simpa using (P ^ 2).neg_mem hsq

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

/- English proof (translation)
Use `haveI := hP`. Establish `hc : p ∣ H.condN` using `h`. Break down `(H.dvd_condN_iff hp).1 hc with hq | rfl | rfl` into its components or cases. Conclude with `H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hp hq P hv`. Conclude with `mem_sq_of_sqrt H.sqq_sq P hP hv`.

Conclude with `mem_sq_of_sqrt H.sqd_sq P hP hv`.
-/
theorem mem_sq_of_dvd_condN {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q * H.d) (P : Ideal (𝓞 H.E)) (hP : P.IsPrime)
    (hv : (p : 𝓞 H.E) ∈ P) : (p : 𝓞 H.E) ∈ P ^ 2 := by
  haveI := hP
  have hc : p ∣ H.condN := h
  rcases (H.dvd_condN_iff hp).1 hc with hq | rfl | rfl
  · exact H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hp hq P hv
  · exact mem_sq_of_sqrt H.sqq_sq P hP hv
  · exact mem_sq_of_sqrt H.sqd_sq P hP hv

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)}`. Use `haveI : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p`. Take `⟨⟨P, hP, hl⟩⟩` from `(inferInstance : Nonempty (pZ.primesOver (𝓞 E)))`. Establish `hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P`.

Rewrite using `[← (Ideal.liesOver_iff P pZ).1 hl]`. Conclude with `Ideal.subset_span rfl`. Establish `hmem : ((p : ℕ) : 𝓞 E) ∈ P` using `by simpa [Ideal.under] using hz`. Establish `hnb : P ≠ ⊥`. Introduce `hb`.

Rewrite `hmem` using `[hb, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hmem)`. Conclude with `⟨⟨P, hP, hnb⟩, hmem⟩`.
-/
theorem exists_place_over (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)}
  haveI : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨⟨P, hP, hl⟩⟩ := (inferInstance : Nonempty (pZ.primesOver (𝓞 E)))
  have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
    rw [← (Ideal.liesOver_iff P pZ).1 hl]
    exact Ideal.subset_span rfl
  have hmem : ((p : ℕ) : 𝓞 E) ∈ P := by simpa [Ideal.under] using hz
  have hnb : P ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  exact ⟨⟨P, hP, hnb⟩, hmem⟩

/- English proof (translation)
Introduce `hd` and use `by obtain ⟨w, hw⟩ := exists_place_over H.E hp exact h w hw (mem_sq_of_dvd_condN H hp hd w.asIdeal w.isPrime hw)`.
-/
theorem not_dvd_condN_of_unram {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal → (p : 𝓞 H.E) ∉ w.asIdeal ^ 2) :
    ¬ p ∣ H.QS * H.q * H.d := fun hd => by
  obtain ⟨w, hw⟩ := exists_place_over H.E hp
  exact h w hw (mem_sq_of_dvd_condN H hp hd w.asIdeal w.isPrime hw)

end UpperTheory.Ram
