import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞)` using `by exact_mod_cast h`. Simplify using `at h'`. Consider the case `coe m`. Establish `h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞)` using `by exact_mod_cast h`.

Establish `h'' : m + 1 ≤ n` using `by exact_mod_cast h'`. Conclude with `(show m < n by omega)` after adjusting the coercions.
-/
theorem withBotENat_lt_of_add_one_le {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP`. Use `hP.multiProj.isPrime` as an intermediate fact. Use `set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) := MvPolynomial.map (IsLocalRing.residue O) with hφdef`. Establish `hφ : Function.Surjective φ` using `MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)}`.

Rewrite using `[hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Use `set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P := (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef`. Establish `hg : Function.Surjective g` using `Ideal.Quotient.mk_surjective.comp hφ`. Establish `hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)}`. Rewrite using `[hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef, Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]`.

Establish `e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P` using `(Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)`. Use `set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef`. Establish `hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Establish `e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)})` using `(Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)`.

Establish `hr0 : r ≠ 0`. Introduce `h0`. Rewrite `h0` using `[hrdef, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmem : ϖ ∈ P.comap (C : O →+* MRing ι O)` using `h0`. Rewrite `hmem` using `[hP.noTorsion, Ideal.mem_bot]`.

Conclude with `hϖ.ne_zero hmem`. Establish `hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P)` using `mem_nonZeroDivisors_of_ne_zero hr0`. Establish `hle` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr`. Rewrite `hle` using `[hP.dim, ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1]`. Conclude with `withBotENat_lt_of_add_one_le hle`.
-/
theorem SpecialDimBound.proof : SpecialDimBound.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  have := hP.multiProj.isPrime
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [hP.dim, ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle
  exact withBotENat_lt_of_add_one_le hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
