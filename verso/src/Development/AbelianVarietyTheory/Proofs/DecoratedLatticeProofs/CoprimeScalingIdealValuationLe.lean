import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

/- English proof (translation)
Establish `h1 : v.valuation F (T : F) = 1`. Establish `: (T : F) = algebraMap (𝓞 F) F (T : 𝓞 F)` using `by simp`. Rewrite using `[this, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 h`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Establish `h2 : Valued.v (algebraMap F (v.adicCompletion F) ((T : F)⁻¹)) = v.valuation F ((T : F)⁻¹)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _`. Rewrite using `[h2, map_inv₀, h1, inv_one]`.
-/
theorem natInv_mem_adicIntegers (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) ((T : F)⁻¹) ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (T : F) = 1 := by
    have : (T : F) = algebraMap (𝓞 F) F (T : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) ((T : F)⁻¹)) = v.valuation F ((T : F)⁻¹) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h2, map_inv₀, h1, inv_one]

/- English proof (translation)
Use `⟨fun w => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV F w _ ∈ w.adicCompletionIntegers F`. Rewrite using `[map_smul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[Algebra.smul_def]`. Conclude with `mul_mem (natInv_mem_adicIntegers F T w h) (h1 w)`. Rewrite using `[h2 w hw, smul_zero]`. Conclude with `zero_mem _`. Rewrite using `[map_smul, h2 w hw, smul_zero]`.
-/
theorem natInv_smul_mem_intAf (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) (α : Af F) (h1 : α ∈ intAf F) (h2 : ∀ w, w ≠ v → evalV F w α = 0) :
    ((T : F)⁻¹ : F) • α ∈ intAf F ∧ ∀ w, w ≠ v → evalV F w (((T : F)⁻¹ : F) • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · change evalV F w _ ∈ w.adicCompletionIntegers F
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      rw [Algebra.smul_def]
      exact mul_mem (natInv_mem_adicIntegers F T w h) (h1 w)
    · rw [h2 w hw, smul_zero]; exact zero_mem _
  · rw [map_smul, h2 w hw, smul_zero]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Conclude with `Prod.ext (mul_zero _) rfl`.
-/
theorem smul_pairA_zero (F : Type) [Field F] [NumberField F] (t : F) (α : Af F) :
    t • pairA F 0 α = pairA F 0 (t • α) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact Prod.ext (mul_zero _) rfl

/- English proof (translation)
Rewrite using `[← smul_pairA_zero, TensorProduct.smul_tmul]`.
-/
theorem pairA_zero_tmul_smul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (t : F) (α : Af F) (c : E) :
    pairA F 0 α ⊗ₜ[F] (t • c) = pairA F 0 (t • α) ⊗ₜ[F] c := by
  rw [← smul_pairA_zero, TensorProduct.smul_tmul]

/- English proof (translation)
Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, h1, h2, a, ha, rfl⟩`. Take `⟨c, hc, rfl⟩` from `FractionalIdeal.mem_singleton_mul.1 ha`. Establish `e : ((T : D.host.E)⁻¹) * c = ((T : D.host.F)⁻¹ : D.host.F) • c`. Rewrite using `[Algebra.smul_def, map_inv₀, map_natCast]`.

Take `⟨g1, g2⟩` from `natInv_smul_mem_intAf D.host.F T v h α h1 h2`. Use `AddSubgroup.subset_closure ⟨((T : D.host.F)⁻¹ : D.host.F) • α, g1, g2, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `pairA_zero_tmul_smul D.host.F D.host.E _ α c`.
-/
theorem idV_natInv_mul_le (D : D7) (𝔠 : FI D) (T : ℕ) (v : Pl D) (h : ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    idV (FractionalIdeal.spanSingleton _ ((T : D.host.E)⁻¹) * 𝔠) v ≤ idV 𝔠 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨c, hc, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 ha
  have e : ((T : D.host.E)⁻¹) * c = ((T : D.host.F)⁻¹ : D.host.F) • c := by
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  obtain ⟨g1, g2⟩ := natInv_smul_mem_intAf D.host.F T v h α h1 h2
  refine AddSubgroup.subset_closure ⟨((T : D.host.F)⁻¹ : D.host.F) • α, g1, g2, c, hc, ?_⟩
  rw [e]
  exact pairA_zero_tmul_smul D.host.F D.host.E _ α c

end GlobalTheory.SeeSaw
