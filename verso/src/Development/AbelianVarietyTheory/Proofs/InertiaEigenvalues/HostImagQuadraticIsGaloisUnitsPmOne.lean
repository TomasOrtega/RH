import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding
open NumberField

namespace GlobalTheory.HostQuadUnits

/- English proof (translation)
Establish `h` using `D.host.hyp.2.2.2.1`. Use linear arithmetic over natural numbers and integers.
-/
theorem four_lt_d (D : Formalism.BasicNotions.D7) : 4 < D.host.d := by
  have h := D.host.hyp.2.2.2.1
  omega

/- English proof (translation)
Establish `h2 : Module.finrank ℚ D.host.K = 2` using `Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D`. Use `⟨?_, fun u => ?_⟩` and prove the remaining obligations. Use `haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨h2⟩ infer_instance`. Set `σ : D.host.K →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := D.host.K)).toRingHom`. Conclude with `GlobalTheory.QuadraticZeta.unit_eq h2 (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.discr_K D) σ (four_lt_d D) u`.
-/
theorem isGalois_and_units (D : Formalism.BasicNotions.D7) :
    IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 := by
  have h2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  refine ⟨?_, fun u => ?_⟩
  · haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨h2⟩
    infer_instance
  · let σ : D.host.K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := D.host.K)).toRingHom
    exact GlobalTheory.QuadraticZeta.unit_eq h2 (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.discr_K D) σ (four_lt_d D) u

/- English proof (translation)
The claim follows from `isGalois_and_units`.
-/
theorem main : ∀ D : Formalism.BasicNotions.D7, IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 :=
  isGalois_and_units

end GlobalTheory.HostQuadUnits
