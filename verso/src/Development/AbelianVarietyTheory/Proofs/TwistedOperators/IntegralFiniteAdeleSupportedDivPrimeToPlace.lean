import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.intAf_div_prime_to_place (D : D7) (v : GlobalTheory.FinPl.Pl D) (d : 𝓞 D.host.F) (hd : d ∉ v.asIdeal)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hsupp : ∀ w, ¬ w = v → evalV D.host.F w α = 0) :
    ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧
      α = α' * algebraMap D.host.F (Af D.host.F) (d : D.host.F) := by
  have hd0 : ((d : D.host.F)) ≠ 0 := by
    intro h
    apply hd
    have : d = 0 := by exact_mod_cast h
    rw [this]; exact v.asIdeal.zero_mem
  have hval : v.valuation D.host.F (d : D.host.F) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  refine ⟨α * algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹, ?_, ?_, ?_⟩
  · intro w
    rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      refine (HeightOneSpectrum.adicCompletionIntegers D.host.F w).mul_mem _ _ (hα w) ?_
      have hv : Valued.v (algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F w) (d : D.host.F)⁻¹)
          = w.valuation D.host.F (d : D.host.F)⁻¹ :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      refine le_of_eq ?_
      refine hv.trans ?_
      rw [map_inv₀, hval, inv_one]
    · rw [hsupp w hw, zero_mul]
      exact (HeightOneSpectrum.adicCompletionIntegers D.host.F w).zero_mem
  · intro w hw
    rw [map_mul, hsupp w hw, zero_mul]
  · rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, mul_one]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem GlobalTheory.intAf_div_prime_to_place' : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (d : 𝓞 D.host.F), d ∉ v.asIdeal → ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) (d : D.host.F) :=
  fun D v d hd α hα hs => GlobalTheory.intAf_div_prime_to_place D v d hd α hα hs
