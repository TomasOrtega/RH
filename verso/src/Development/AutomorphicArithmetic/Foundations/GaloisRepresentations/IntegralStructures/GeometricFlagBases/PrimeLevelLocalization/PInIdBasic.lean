import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.InIdBasic

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {E : Type} [Field E] [NumberField E] (w : Plc E)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem valued_algebraMap_adicCompletionIntegers_eq_intValuation (r : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) r : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E) w r]
  exact HeightOneSpectrum.adicCompletion.valued_coe _ _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem inId_iff_le (𝔟 : Ideal (𝓞 E)) (y : w.adicCompletion E) : InId w 𝔟 y ↔ ∃ x ∈ 𝔟, Valued.v y ≤ w.intValuation x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ Submodule.span _ _ at hz
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨x, hx, (valued_algebraMap_adicCompletionIntegers_eq_intValuation w x).le⟩
    | zero => exact ⟨0, 𝔟.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x1, h1, e1⟩ := ha
      obtain ⟨x2, h2, e2⟩ := hb
      have hab : Valued.v (((a + b : w.adicCompletionIntegers E)) : w.adicCompletion E) ≤
          max (Valued.v (a : w.adicCompletion E)) (Valued.v (b : w.adicCompletion E)) :=
        Valuation.map_add Valued.v (a : w.adicCompletion E) (b : w.adicCompletion E)
      rcases le_total (w.intValuation x1) (w.intValuation x2) with h | h
      · exact ⟨x2, h2, hab.trans (max_le (e1.trans h) e2)⟩
      · exact ⟨x1, h1, hab.trans (max_le e1 (e2.trans h))⟩
    | smul c a _ ha =>
      obtain ⟨x, hx, e⟩ := ha
      refine ⟨x, hx, ?_⟩
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      have hm : Valued.v (((c • a : w.adicCompletionIntegers E)) : w.adicCompletion E) =
          Valued.v (c : w.adicCompletion E) * Valued.v (a : w.adicCompletion E) :=
        Valuation.map_mul Valued.v (c : w.adicCompletion E) (a : w.adicCompletion E)
      rw [hm]
      exact (mul_le_of_le_one_left' hc).trans e
  · rintro ⟨x, hx, hle⟩
    have hy : y ∈ w.adicCompletionIntegers E :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hle.trans (w.intValuation_le_one x))
    by_cases h0 : w.intValuation x = 0
    · rw [h0, le_zero_iff, Valuation.zero_iff] at hle
      exact ⟨0, Ideal.zero_mem _, by simp [hle]⟩
    · set a : w.adicCompletionIntegers E := algebraMap (𝓞 E) (w.adicCompletionIntegers E) x with ha_def
      have ha : Valued.v (a : w.adicCompletion E) = w.intValuation x := valued_algebraMap_adicCompletionIntegers_eq_intValuation w x
      have ha0 : (a : w.adicCompletion E) ≠ 0 := by
        intro h
        apply h0
        rw [← ha, h, map_zero]
      have hq : y / (a : w.adicCompletion E) ∈ w.adicCompletionIntegers E := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, ha]
        exact div_le_one_of_le₀ hle zero_le'
      refine ⟨⟨_, hq⟩ * a, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hx), ?_⟩
      simp only [MulMemClass.coe_mul]
      exact div_mul_cancel₀ y ha0

end

end UpperTheory.Gal.Int.Geo.Pl
