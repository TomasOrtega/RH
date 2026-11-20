import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffMult
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MemRam
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiff

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Establish `h1 : (n : 𝓞 M) = algebraMap ℤ (𝓞 M) (n : ℤ)` using `by simp`. Rewrite using `[h1, ← Ideal.mem_comap, ← Ideal.under_def, ← h.over, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]`.
-/
private theorem natMem {M : Type} [Field M] [NumberField M] (l : ℕ) (P : Ideal (𝓞 M))
    [h : P.LiesOver (span {(l : ℤ)})] (n : ℕ) : (n : 𝓞 M) ∈ P ↔ l ∣ n := by
  have h1 : (n : 𝓞 M) = algebraMap ℤ (𝓞 M) (n : ℤ) := by simp
  rw [h1, ← Ideal.mem_comap, ← Ideal.under_def, ← h.over, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h2` using `H.sqd_sq`. Rewrite `h2` using `[← hs]`. Rewrite using `[← pow_two]`. Use `push_cast`.

Conclude with `h2`.
-/
private theorem sq_lemma' {φ : Frame} (H : HostAx φ) (s : 𝓞 H.E) (hs : (s : H.E) = H.sqd) :
    s * s = -(H.d : 𝓞 H.E) := by
  apply RingOfIntegers.coe_injective
  have h2 := H.sqd_sq
  rw [← hs] at h2
  rw [← pow_two]
  push_cast
  exact h2

/- English proof (translation)
Introduce `φ H`. Establish `hd` using `H.der`. Take `⟨-, s, hs, -, hdiff⟩` from `discr_K H`. Establish `key : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.LiesOver (span {(l : ℤ)})], ¬ P ∣ span {s}`. Introduce `l hl hld P _ hPs`.

Rewrite `hPs` using `[Ideal.dvd_span_singleton]`. Establish `hsq : s * s ∈ P` using `P.mul_mem_left s hPs`. Rewrite `hsq` using `[sq_lemma' H s hs, neg_mem_iff, natMem l P]`. Conclude with `hld ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 hsq)`. Establish `mult : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) = multiplicity P (differentIdeal ℤ (𝓞 H.E))`.

Introduce `l hl hld P hPp _`. Establish `hP0 : P ≠ ⊥`. Introduce `h0`. Establish `hl' : (l : 𝓞 H.E) ∈ P` using `(natMem l P l).2 dvd_rfl`. Rewrite `hl'` using `[h0, Ideal.mem_bot]`.

Conclude with `hl.ne_zero (by exact_mod_cast hl')`. Establish `hpr : Prime P` using `Ideal.prime_of_isPrime hP0 hPp`. Establish `hz : emultiplicity P (span {s}) = 0` using `emultiplicity_eq_zero.2 (key l hl hld P)`. Unfold `multiplicity`. Rewrite using `[hdiff, emultiplicity_mul hpr, hz, add_zero]`.

Use `⟨fun σ => Formalism.HC.Der.kc_diff_smul_eq H.toHostRaw σ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hPp`. Prove the components needed by the constructor for the conclusion. Introduce `hPd`. Establish `hmem` using `hd.diffSupport P hPp hPd`.

Establish `hne : H.QS * H.q ≠ 0` using `mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero`. Take `⟨l, hl, hlq, hover⟩` from `Formalism.HC.Der.kc_exists_prime P _ hne hmem`. Use `⟨l, ?_, hover⟩` and prove the remaining obligations. Establish `hld : l ≠ H.d`. Introduce and unpack `rfl`.

Conclude with `H.d_not_dvd_QSq hlq`. Simplify using `only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase]`. Use `⟨hld, ?_⟩` and prove the remaining obligations. Rewrite using `[(mem_ram H hl).1]`. Introduce `hel`.

Establish `h0 : multiplicity P (differentIdeal ℤ (𝓞 H.E)) = 0`. Rewrite using `[(diff_mult H hl P).2.2.1 (by rw [hel]; exact hl.not_dvd_one), hel]`. Establish `hdv : P ∣ differentIdeal ℤ (𝓞 H.E)` using `hdiff ▸ dvd_mul_of_dvd_left hPd _`. Conclude with `multiplicity_eq_zero.1 h0 hdv`. Introduce and unpack `⟨l, hlI, hover⟩`.

Simplify using `only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase] at hlI`. Take `⟨hld, hlr⟩` from `hlI`. Establish `hl : l.Prime`. Simplify using `only [UpperTheory.HF.Formalism.HC.HostRaw.ram, Nat.mem_primeFactors] at hlr`. Conclude with `hlr.1`.

Establish `hv : H.vdH l ≠ 0` using `((mem_ram H hl).2.2.1).1 hlr`. Establish `hm` using `(diff_mult H hl P).1`. Establish `hne : (H.el l : ℝ) * H.vdH l ≠ 0` using `mul_ne_zero (by exact_mod_cast (UpperTheory.HF.Formalism.HC.HostRaw.el_pos H.toHostRaw l).ne') hv`. Rewrite `hne` using `[← hm, ← mult l hl hld P]`. Assume the negation of the conclusion as `hnd`.

Conclude with `hne (by exact_mod_cast multiplicity_eq_zero.2 hnd)`. Introduce `l hl hld P _ _`. Rewrite using `[mult l hl hld P]`. Conclude with `(diff_mult H hl P).1`. Simplify using `only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase, UpperTheory.HF.Formalism.HC.HostRaw.ram, Nat.mem_primeFactors]`.

Use `⟨H.d_ne_two.symm, Nat.prime_two, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Int.ofNat_dvd_left.1 hd.discr_primes.2.1`. Conclude with `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)`.
-/
theorem UpperTheory.HF.diff_EK_supp :
    ∀ {φ : Frame} (H : HostAx φ), (∀ σ : H.E ≃ₐ[ℚ] H.E, σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ (∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) : ℝ) = H.el l * H.vdH l) ∧ 2 ∈ H.ramI := by
  intro φ H
  have hd := H.der
  obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
  have key : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.LiesOver (span {(l : ℤ)})],
      ¬ P ∣ span {s} := by
    intro l hl hld P _ hPs
    rw [Ideal.dvd_span_singleton] at hPs
    have hsq : s * s ∈ P := P.mul_mem_left s hPs
    rw [sq_lemma' H s hs, neg_mem_iff, natMem l P] at hsq
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 hsq)
  have mult : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})],
      multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) = multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
    intro l hl hld P hPp _
    have hP0 : P ≠ ⊥ := by
      intro h0
      have hl' : (l : 𝓞 H.E) ∈ P := (natMem l P l).2 dvd_rfl
      rw [h0, Ideal.mem_bot] at hl'
      exact hl.ne_zero (by exact_mod_cast hl')
    have hpr : Prime P := Ideal.prime_of_isPrime hP0 hPp
    have hz : emultiplicity P (span {s}) = 0 := emultiplicity_eq_zero.2 (key l hl hld P)
    unfold multiplicity
    rw [hdiff, emultiplicity_mul hpr, hz, add_zero]
  refine ⟨fun σ => Formalism.HC.Der.kc_diff_smul_eq H.toHostRaw σ, ?_, ?_, ?_⟩
  · intro P hPp
    constructor
    · intro hPd
      have hmem := hd.diffSupport P hPp hPd
      have hne : H.QS * H.q ≠ 0 := mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
      obtain ⟨l, hl, hlq, hover⟩ := Formalism.HC.Der.kc_exists_prime P _ hne hmem
      refine ⟨l, ?_, hover⟩
      have hld : l ≠ H.d := by
        rintro rfl
        exact H.d_not_dvd_QSq hlq
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase]
      refine ⟨hld, ?_⟩
      rw [(mem_ram H hl).1]
      intro hel
      have h0 : multiplicity P (differentIdeal ℤ (𝓞 H.E)) = 0 := by
        rw [(diff_mult H hl P).2.2.1 (by rw [hel]; exact hl.not_dvd_one), hel]
      have hdv : P ∣ differentIdeal ℤ (𝓞 H.E) := hdiff ▸ dvd_mul_of_dvd_left hPd _
      exact multiplicity_eq_zero.1 h0 hdv
    · rintro ⟨l, hlI, hover⟩
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase] at hlI
      obtain ⟨hld, hlr⟩ := hlI
      have hl : l.Prime := by
        simp only [UpperTheory.HF.Formalism.HC.HostRaw.ram, Nat.mem_primeFactors] at hlr
        exact hlr.1
      have hv : H.vdH l ≠ 0 := ((mem_ram H hl).2.2.1).1 hlr
      have hm := (diff_mult H hl P).1
      have hne : (H.el l : ℝ) * H.vdH l ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (UpperTheory.HF.Formalism.HC.HostRaw.el_pos H.toHostRaw l).ne') hv
      rw [← hm, ← mult l hl hld P] at hne
      by_contra hnd
      exact hne (by exact_mod_cast multiplicity_eq_zero.2 hnd)
  · intro l hl hld P _ _
    rw [mult l hl hld P]
    exact (diff_mult H hl P).1
  · simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase, UpperTheory.HF.Formalism.HC.HostRaw.ram,
      Nat.mem_primeFactors]
    refine ⟨H.d_ne_two.symm, Nat.prime_two, ?_, ?_⟩
    · exact Int.ofNat_dvd_left.1 hd.discr_primes.2.1
    · exact Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)
