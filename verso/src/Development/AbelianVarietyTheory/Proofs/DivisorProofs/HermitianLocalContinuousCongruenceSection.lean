import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hI0 : Ideal.span {f} ≠ (0 : Ideal B)`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hf`. Establish `hPu : ¬ IsUnit P`. Rewrite using `[Ideal.isUnit_iff]`.

Conclude with `hP.ne_top`. Establish `hfin : FiniteMultiplicity P (Ideal.span {f})` using `FiniteMultiplicity.of_not_isUnit hPu hI0`. Establish `key : ¬ P ^ (multiplicity P (Ideal.span {f}) + 1) ∣ Ideal.span {f}` using `hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)`. Establish `hdvd : P ^ (multiplicity P (Ideal.span {f})) ∣ Ideal.span {f}` using `pow_multiplicity_dvd P _`. Generalize the expression as in `multiplicity P (Ideal.span {f}) = m at key hdvd`.

Take `⟨J, hJ⟩` from `hdvd`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hJP : ¬ J ≤ P`. Introduce `hle`. Establish `hd : P ∣ J` using `Ideal.dvd_iff_le.mpr hle`.

Apply `key` to reduce the goal to its premises. Rewrite using `[hJ, pow_succ]`. Conclude with `mul_dvd_mul_left _ hd`. Take `⟨s, hsJ, hsP⟩` from `Set.not_subset.mp hJP`. Introduce `b hb`.

Use `⟨s, hsP, ?_⟩` and prove the remaining obligations. Establish `hmem : b * s ∈ P ^ m * J` using `Ideal.mul_mem_mul hb hsJ`. Rewrite `hmem` using `[← hJ]`. Rewrite using `[mul_comm]`. Conclude with `hmem`.
-/
theorem dedekind_pow_maximal_mul_mem_span (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) (P : Ideal B) (hP : P.IsMaximal) :
    ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  classical
  have hI0 : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hf
  have hPu : ¬ IsUnit P := by
    rw [Ideal.isUnit_iff]; exact hP.ne_top
  have hfin : FiniteMultiplicity P (Ideal.span {f}) := FiniteMultiplicity.of_not_isUnit hPu hI0
  have key : ¬ P ^ (multiplicity P (Ideal.span {f}) + 1) ∣ Ideal.span {f} :=
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  have hdvd : P ^ (multiplicity P (Ideal.span {f})) ∣ Ideal.span {f} := pow_multiplicity_dvd P _
  generalize multiplicity P (Ideal.span {f}) = m at key hdvd
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨m, ?_⟩
  have hJP : ¬ J ≤ P := by
    intro hle
    have hd : P ∣ J := Ideal.dvd_iff_le.mpr hle
    apply key
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left _ hd
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  intro b hb
  refine ⟨s, hsP, ?_⟩
  have hmem : b * s ∈ P ^ m * J := Ideal.mul_mem_mul hb hsJ
  rw [← hJ] at hmem
  rw [mul_comm]
  exact hmem

end GlobalTheory
