import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `hle hdim hdom`. Use `set I := (maximalIdeal R).map (algebraMap R A) with hI`. Use `haveI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).1 hdom`. Establish `hp1 : p.height = 1`. Establish `h` using `IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)`.

Rewrite `h` using `[hdim]`. Conclude with `h.symm` after adjusting the coercions. Use `haveI : p.FiniteHeight := by`. Rewrite using `[Ideal.finiteHeight_iff]`. Use `right`.

Rewrite using `[hp1]`. Conclude with `ENat.one_ne_top`. Use `haveI : I.FiniteHeight := Ideal.finiteHeight_of_le hle (Ideal.IsPrime.ne_top ‹_›)`. Establish `hIne : I ≠ ⊥`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`.

Establish `hmem : ϖ ∈ maximalIdeal R`. Rewrite using `[hϖ.maximalIdeal_eq]`. Conclude with `Ideal.mem_span_singleton_self ϖ`. Establish `hreg : IsSMulRegular A ϖ` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)`. Establish `hne : algebraMap R A ϖ ≠ 0`.

Introduce `h0`. Establish `: ϖ • (1 : A) = ϖ • (0 : A)` using `by rw [Algebra.smul_def, mul_one, h0, smul_zero]`. Conclude with `one_ne_zero (hreg this)`. Introduce `hbot`. Apply `hne` to reduce the goal to its premises.

Establish `: algebraMap R A ϖ ∈ I` using `Ideal.mem_map_of_mem _ hmem`. Rewrite `this` using `[hbot]`. Conclude with `(Ideal.mem_bot).1 this`. Establish `hIh : 1 ≤ I.height`. Rewrite using `[ENat.one_le_iff_ne_zero]`.

Introduce `h0`. Conclude with `hIne (Ideal.height_eq_zero_iff_eq_bot.1 h0)`. Conclude with `(Ideal.eq_of_le_of_height_le I hle (by rw [hp1]; exact hIh)).symm`.
-/
theorem eq_map_maximalIdeal_of_ringKrullDim_eq_one (R A : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A]
    (p : Ideal A) [p.IsPrime] :
    (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 →
      IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) →
      p = (maximalIdeal R).map (algebraMap R A) := by
  intro hle hdim hdom
  set I := (maximalIdeal R).map (algebraMap R A) with hI
  haveI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).1 hdom
  have hp1 : p.height = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    rw [hdim] at h
    exact_mod_cast h.symm
  haveI : p.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hp1]; exact ENat.one_ne_top
  haveI : I.FiniteHeight := Ideal.finiteHeight_of_le hle (Ideal.IsPrime.ne_top ‹_›)

  have hIne : I ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmem : ϖ ∈ maximalIdeal R := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have hreg : IsSMulRegular A ϖ :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have hne : algebraMap R A ϖ ≠ 0 := by
      intro h0
      have : ϖ • (1 : A) = ϖ • (0 : A) := by rw [Algebra.smul_def, mul_one, h0, smul_zero]
      exact one_ne_zero (hreg this)
    intro hbot
    apply hne
    have : algebraMap R A ϖ ∈ I := Ideal.mem_map_of_mem _ hmem
    rw [hbot] at this
    exact (Ideal.mem_bot).1 this
  have hIh : 1 ≤ I.height := by
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    exact hIne (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  exact (Ideal.eq_of_le_of_height_le I hle (by rw [hp1]; exact hIh)).symm

end GlobalTheory
