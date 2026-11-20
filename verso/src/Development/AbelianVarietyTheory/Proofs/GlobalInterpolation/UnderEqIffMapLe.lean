import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem under_eq_iff_map_le (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro rfl
    exact le_rfl
  · intro h
    apply HeightOneSpectrum.ext
    exact (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top h).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem under_eq_iff (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ (Q = P ∨ Q = P') := by
  rw [under_eq_iff_map_le, h, Q.isPrime.mul_le]
  refine or_congr ⟨fun h => ?_, fun h => h ▸ le_rfl⟩ ⟨fun h => ?_, fun h => h ▸ le_rfl⟩
  · exact HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
  · exact HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem not_mul_le_sq (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P') :
    ¬ P.asIdeal * P'.asIdeal ≤ P.asIdeal ^ 2 := by
  intro h
  rw [← Ideal.dvd_iff_le, sq, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at h
  exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h).symm)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem val_eq_inv_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)),
    χ.TrivOn F → χ.UnrAt P → χ.UnrAt P' → P ≠ P' →
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal → χ.val P' = (χ.val P)⁻¹ := by
  intro F E _ _ _ _ _ χ v P P' hχ h1 h2 hne hv
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hab : aboveF (L := E) F v = {P, P'} := by
    ext Q
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff v P P' hv Q
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → χ.UnrAt Q →
      ¬ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal ^ 2 →
      χ.locK Q (upF F (Units.mk0 π h0)) = χ.val Q := by
    intro Q hQ hunr hu
    refine χ.val_eq hunr _ ?_
    subst hQ
    show Valued.v ((algebraMap F E π : E) : Q.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.MuConj.valuation_up Q hu, hπ]
  have h := hχ.1 v (Units.mk0 π h0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hne,
    key P ((under_eq_iff v P P' hv _).2 (Or.inl rfl)) h1 (hv ▸ not_mul_le_sq P P' hne),
    key P' ((under_eq_iff v P P' hv _).2 (Or.inr rfl)) h2
      (by rw [hv, mul_comm]; exact not_mul_le_sq P' P hne.symm)] at h
  exact eq_inv_of_mul_eq_one_right h

end GlobalTheory.HeckeSplit
