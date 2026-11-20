import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FieldCompatibleIffWdRel

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt.Inhab

abbrev QI : Type := CyclotomicField 4 ℚ

instance : IsGalois ℚ QI := IsCyclotomicExtension.isGalois {4} ℚ QI

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the decidable proposition.
-/
theorem finrank_QI : Module.finrank ℚ QI = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 QI]; decide

def threeZ : Ideal ℤ := Ideal.span {((3 : ℕ) : ℤ)}

instance : threeZ.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).2 (Nat.prime_iff_prime_int.mp Nat.prime_three)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem threeZ_ne_bot : threeZ ≠ ⊥ := by
  simp [threeZ]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem ncard_primesOver_threeZ : (threeZ.primesOver (𝓞 QI)).ncard = 1 := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn threeZ (𝓞 QI) (QI ≃ₐ[ℚ] QI)
  have hf := IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 4) 3 QI (by norm_num)
  have ho : orderOf ((3 : ℕ) : ZMod 4) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hc : Nat.card (QI ≃ₐ[ℚ] QI) = 2 := by rw [IsGalois.card_aut_eq_finrank, finrank_QI]
  rw [show threeZ = Ideal.span {((3 : ℕ) : ℤ)} from rfl, hf, ho, hc, ← mul_assoc] at h
  exact Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_right two_pos (h.trans (one_mul 2).symm))

def primeAbove3 : threeZ.primesOver (𝓞 QI) := (Ideal.nonempty_primesOver (S := 𝓞 QI) threeZ).some

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem primeAbove3_ne_bot : (primeAbove3 : Ideal (𝓞 QI)) ≠ ⊥ := by
  intro h0
  have hov := (primeAbove3.2.2).over
  rw [h0, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 QI))] at hov
  exact threeZ_ne_bot hov

def placeAbove3 : HeightOneSpectrum (𝓞 QI) := ⟨primeAbove3.1, primeAbove3.2.1, primeAbove3_ne_bot⟩

def place3 : HeightOneSpectrum (𝓞 ℚ) := placeAbove3.under (𝓞 ℚ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem placeAbove3_under_int : placeAbove3.asIdeal.under ℤ = threeZ :=
  (primeAbove3.2.2).over.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem three_mem_place3 : (3 : 𝓞 ℚ) ∈ place3.asIdeal := by
  rw [place3, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_ofNat]
  have h3 : ((3 : ℕ) : ℤ) ∈ placeAbove3.asIdeal.under ℤ := by
    rw [placeAbove3_under_int]; exact Ideal.subset_span rfl
  rw [Ideal.under_def, Ideal.mem_comap] at h3
  simpa using h3

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cycAt_three : CycAt place3 placeAbove3 := by
  refine ⟨inferInstance, by rw [finrank_QI]; exact Nat.prime_two, rfl, fun u' hu' => ?_⟩
  have hu'3 : u'.asIdeal.under ℤ = threeZ := by
    rw [← Ideal.under_under (B := 𝓞 ℚ), ← HeightOneSpectrum.under_asIdeal, hu', place3,
      HeightOneSpectrum.under_asIdeal, Ideal.under_under, placeAbove3_under_int]
  have m1 : u'.asIdeal ∈ threeZ.primesOver (𝓞 QI) := ⟨u'.isPrime, ⟨hu'3.symm⟩⟩
  have m2 : placeAbove3.asIdeal ∈ threeZ.primesOver (𝓞 QI) := primeAbove3.2
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 ncard_primesOver_threeZ
  rw [ha] at m1 m2
  exact HeightOneSpectrum.ext (m1.trans m2.symm)

section Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end Loc

end GlobalTheory.FunExt.Inhab

end
