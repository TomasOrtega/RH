import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h⟩`. Rewrite using `[GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, h]`. Introduce `h`. Establish `h0 : c ≠ 0`.

Introduce and unpack `rfl`. Rewrite `h` using `[map_zero]`. Conclude with `exp_ne_zero h.symm`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, exp_inj]`.

Conclude with `neg_injective h`.
-/
theorem isLocGen_iff_valuation_eq (p : HeightOneSpectrum (𝓞 K)) (c : K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    IsLocGen p c I ↔ p.valuation K c = exp (-FractionalIdeal.count K p I) := by
  constructor
  · rintro ⟨h0, h⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, h]
  · intro h
    have h0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact exp_ne_zero h.symm
    refine ⟨h0, ?_⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, exp_inj] at h
    exact neg_injective h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨y, hy, hv⟩` from `GlobalTheory.Idele.exists_mem_valuation_eq hI p`. Establish `hvy : p.valuation K y ≠ 0` using `by rw [hv]; exact exp_ne_zero`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hvy`.

Establish `h1 : p.valuation K (c / y) ≤ 1`. Rewrite using `[map_div₀, div_le_one₀ (zero_lt_iff.2 hvy), hv]`. Conclude with `h`. Take `⟨a, s, hs⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p (c / y) h1`. Use `⟨s.1, s.2, ?_⟩` and prove the remaining obligations.

Establish `: (s.1 : 𝓞 K) • c = a • y`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, ← hs]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Submodule.smul_mem (I : Submodule (𝓞 K) K) a hy`.

Introduce and unpack `⟨s, hs, hc⟩`. Establish `h` using `(GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hc p`. Establish `h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1`. Use `le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)` and prove the remaining obligations. Conclude with `(p.valuation_lt_one_iff_mem s).1 hlt`.

Rewrite `h` using `[Algebra.smul_def, map_mul, h1, one_mul]`. Then use the resulting hypothesis.
-/
theorem valuation_le_iff_exists_smul_mem (p : HeightOneSpectrum (𝓞 K)) {I : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) (c : K) :
    p.valuation K c ≤ exp (-FractionalIdeal.count K p I) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    have hvy : p.valuation K y ≠ 0 := by rw [hv]; exact exp_ne_zero
    have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
    have h1 : p.valuation K (c / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvy), hv]; exact h
    obtain ⟨a, s, hs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p (c / y) h1
    refine ⟨s.1, s.2, ?_⟩
    have : (s.1 : 𝓞 K) • c = a • y := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hs]
      field_simp
    rw [this]
    exact Submodule.smul_mem (I : Submodule (𝓞 K) K) a hy
  · rintro ⟨s, hs, hc⟩
    have h := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hc p
    have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
      exact (p.valuation_lt_one_iff_mem s).1 hlt
    rwa [Algebra.smul_def, map_mul, h1, one_mul] at h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz p`. Conclude with `⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hz⟩`. Introduce `h`. Set `A : Ideal (𝓞 K)` to `Λ.comap (LinearMap.toSpanSingleton (𝓞 K) V z)`.

Establish `hA : A = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hAm⟩` from `Ideal.exists_le_maximal A hne`. Establish `hm0 : m ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)`. Take `⟨s, hs, hsz⟩` from `h ⟨m, hm.isPrime, hm0⟩`.

Conclude with `hs (hAm (by simpa [A] using hsz))`. Establish `: (1 : 𝓞 K) ∈ A` using `hA ▸ Submodule.mem_top`. Simplify `this` using `[A]`.
-/
theorem mem_iff_forall_exists_smul_mem {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (Λ : Submodule (𝓞 K) V) (z : V) :
    z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  constructor
  · intro hz p
    exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hz⟩
  · intro h
    let A : Ideal (𝓞 K) := Λ.comap (LinearMap.toSpanSingleton (𝓞 K) V z)
    have hA : A = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hAm⟩ := Ideal.exists_le_maximal A hne
      have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
      obtain ⟨s, hs, hsz⟩ := h ⟨m, hm.isPrime, hm0⟩
      exact hs (hAm (by simpa [A] using hsz))
    have : (1 : 𝓞 K) ∈ A := hA ▸ Submodule.mem_top
    simpa [A] using this

/- English proof (translation)
Introduce `K _ _`. Use `⟨fun I cl hI hcl c => ?_, fun I p hI => ⟨?_, fun cl => ?_⟩, fun V _ _ Λ z => mem_iff_forall_exists_smul_mem Λ z⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Idele.mem_iff_valuation_le hI]`. Use `forall_congr' fun p => ?_` and prove the remaining obligations. Rewrite using `[(isLocGen_iff_valuation_eq p _ I).1 (hcl p)]`.

Take `⟨y, hy, hv⟩` from `GlobalTheory.Idele.exists_mem_valuation_eq hI p`. Conclude with `⟨y, hy, (isLocGen_iff_valuation_eq p y I).2 hv⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h.1, fun c => ?_⟩` and prove the remaining obligations.

Rewrite using `[(isLocGen_iff_valuation_eq p _ I).1 h]`. Conclude with `valuation_le_iff_exists_smul_mem p hI c`. Introduce and unpack `⟨-, h⟩`. Take `⟨y, hy, hv⟩` from `GlobalTheory.Idele.exists_mem_valuation_eq hI p`. Use `(isLocGen_iff_valuation_eq p cl I).2 (le_antisymm ?_ ?_)` and prove the remaining obligations.

Conclude with `(valuation_le_iff_exists_smul_mem p hI cl).2 ((h cl).1 le_rfl)`. Rewrite using `[← hv]`. Conclude with `(h y).2 ((valuation_le_iff_exists_smul_mem p hI y).1 hv.le)`.
-/
theorem local_global_ideal_lattice : ∀ (K : Type) [Field K] [NumberField K],
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (cl : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
      (∀ p, IsLocGen p (cl p) I) → ∀ c : K,
        c ∈ I ↔ ∀ p : HeightOneSpectrum (𝓞 K), p.valuation K c ≤ p.valuation K (cl p)) ∧
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (p : HeightOneSpectrum (𝓞 K)), I ≠ 0 →
      (∃ cl ∈ I, IsLocGen p cl I) ∧ ∀ cl, IsLocGen p cl I ↔ cl ≠ 0 ∧ ∀ c : K,
        p.valuation K c ≤ p.valuation K cl ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I) ∧
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 K) V] (Λ : Submodule (𝓞 K) V) (z : V),
      z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  intro K _ _
  refine ⟨fun I cl hI hcl c => ?_, fun I p hI => ⟨?_, fun cl => ?_⟩,
    fun V _ _ Λ z => mem_iff_forall_exists_smul_mem Λ z⟩
  · rw [GlobalTheory.Idele.mem_iff_valuation_le hI]
    refine forall_congr' fun p => ?_
    rw [(isLocGen_iff_valuation_eq p _ I).1 (hcl p)]
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    exact ⟨y, hy, (isLocGen_iff_valuation_eq p y I).2 hv⟩
  · constructor
    · intro h
      refine ⟨h.1, fun c => ?_⟩
      rw [(isLocGen_iff_valuation_eq p _ I).1 h]
      exact valuation_le_iff_exists_smul_mem p hI c
    · rintro ⟨-, h⟩
      obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
      refine (isLocGen_iff_valuation_eq p cl I).2 (le_antisymm ?_ ?_)
      · exact (valuation_le_iff_exists_smul_mem p hI cl).2 ((h cl).1 le_rfl)
      · rw [← hv]
        exact (h y).2 ((valuation_le_iff_exists_smul_mem p hI y).1 hv.le)

end GlobalTheory.LamF
