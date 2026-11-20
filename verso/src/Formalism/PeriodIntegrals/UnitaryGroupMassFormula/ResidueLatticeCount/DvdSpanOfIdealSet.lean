import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical

noncomputable section

namespace PI.Residue

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dvd_span_of_idealSet (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    (J : Ideal (𝓞 K)) ∣ Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} := by
  rw [Ideal.dvd_span_singleton]
  exact preimage_of_IdealSetMap K J x

def cof (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) : Ideal (𝓞 K) :=
  (dvd_span_of_idealSet J x).choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cof_spec (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} = (J : Ideal (𝓞 K)) * cof J x :=
  (dvd_span_of_idealSet J x).choose_spec

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cof_mem (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) : cof J x ∈ (Ideal (𝓞 K))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have h1 := cof_spec J x
  rw [h, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h1
  exact nonZeroDivisors.coe_ne_zero _ h1

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cof_class (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) (C : ClassGroup (𝓞 K))
    (hJ : ClassGroup.mk0 J = C⁻¹) : ClassGroup.mk0 ⟨cof J x, cof_mem J x⟩ = C := by
  have h1 : ClassGroup.mk0 (J * ⟨cof J x, cof_mem J x⟩) = 1 := by
    rw [ClassGroup.mk0_eq_one_iff]
    have : ((J * ⟨cof J x, cof_mem J x⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
        Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} := (cof_spec J x).symm
    rw [this]
    exact ⟨⟨_, rfl⟩⟩
  rw [map_mul, hJ] at h1
  exact (inv_mul_eq_one.mp h1).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem norm_eq_cof (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    mixedEmbedding.norm (x : mixedSpace K) =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * (Ideal.absNorm (cof J x) : ℝ) := by
  rw [← Nat.cast_mul, ← map_mul, ← cof_spec, Ideal.absNorm_span_singleton,
    ← idealSetMap_apply K J x, ← intNorm_coe, intNorm]

def toPair (J : (Ideal (𝓞 K))⁰) (C : ClassGroup (𝓞 K)) (hJ : ClassGroup.mk0 J = C⁻¹)
    (x : idealSet K J) : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K :=
  (⟨⟨cof J x, cof_mem J x⟩, cof_class J x C hJ⟩, (integerSetEquiv K (idealSetMap K J x)).2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toPair_injective (J : (Ideal (𝓞 K))⁰) (C : ClassGroup (𝓞 K))
    (hJ : ClassGroup.mk0 J = C⁻¹) : Function.Injective (toPair J C hJ) := by
  intro x y h
  have h1 : cof J x = cof J y := by
    have := congrArg (fun p => ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) h
    exact this
  have h2 : (integerSetEquiv K (idealSetMap K J x)).2 = (integerSetEquiv K (idealSetMap K J y)).2 :=
    congrArg (fun p : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K => p.2) h
  have h3 : (integerSetEquiv K (idealSetMap K J x)).1 = (integerSetEquiv K (idealSetMap K J y)).1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [integerSetEquiv_apply_fst, integerSetEquiv_apply_fst, cof_spec, cof_spec, h1]
  have h4 : idealSetMap K J x = idealSetMap K J y := (integerSetEquiv K).injective (Prod.ext h3 h2)
  apply Subtype.ext
  rw [← idealSetMap_apply K J x, ← idealSetMap_apply K J y, h4]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem idealSetSum : IdealSetSum := by
  intro K _ _ s C J hJ
  set g : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-s)) *
      ENNReal.ofReal ((Ideal.absNorm ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) with hg
  have h1 : ∀ x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s)) =
      g (toPair J C hJ x) := by
    intro x
    rw [norm_eq_cof, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (by positivity)]
    rfl
  calc ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))
      = ∑' x : idealSet K J, g (toPair J C hJ x) := tsum_congr h1
    _ ≤ ∑' p, g p := ENNReal.tsum_comp_le_tsum_of_injective (toPair_injective J C hJ) g
    _ = _ := by
      rw [ENNReal.tsum_prod', classZeta, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun I => ?_
      have : Fintype (torsion K) := Fintype.ofFinite _
      rw [tsum_fintype]
      simp only [hg]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
        Nat.card_eq_fintype_card, mul_assoc]

end PI.Residue
