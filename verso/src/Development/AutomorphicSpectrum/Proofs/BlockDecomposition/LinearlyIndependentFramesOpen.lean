import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lip_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : PI.VolStabS.TensAllW.LIP S) : PI.VolStabS.TensAllW.LIP R := by
  intro m n _ _ _ _ W hW
  obtain ⟨P, hP⟩ := h m n (W.map e) (by
    intro c hc
    have hc' : W *ᵥ (fun j => e.symm (c j)) = 0 := by
      funext i
      apply e.injective
      have := congrFun hc i
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum] using this
    have h0 := hW _ hc'
    funext j
    have := congrFun h0 j
    simpa using this)
  refine ⟨P.map e.symm, ?_⟩
  ext i j
  apply e.injective
  have := congrFun (congrFun hP i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  rw [Matrix.mul_apply, map_sum]
  simp only [map_mul, Matrix.map_apply, RingEquiv.apply_symm_apply]
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem lip_of_artinian_reduced (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R] :
    PI.VolStabS.TensAllW.LIP R := by
  classical
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  letI : ∀ m : MaximalSpectrum R, Field (R ⧸ m.asIdeal) := fun m =>
    Ideal.Quotient.field m.asIdeal
  exact lip_of_ringEquiv (IsArtinianRing.equivPi R)
    (PI.VolStabS.TensAllW.lip_pi (fun m : MaximalSpectrum R => R ⧸ m.asIdeal)
      (fun m => PI.VolStabS.TensAllW.lip_field _))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isOpen_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ hR n M
  obtain ⟨hT, -, -, -, hA, hRed, hU, -⟩ := hR
  haveI := hT
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hUo : IsOpen {r : R | IsUnit r} := by
    have := hU.isOpen_range
    convert this using 1
    ext r
    simp [IsUnit]
  exact PI.VolStabS.TensAllW.isOpen_linIndep (Module.finBasis F E) R hUo
    (lip_of_artinian_reduced R)

end GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen
