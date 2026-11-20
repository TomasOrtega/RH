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
Introduce `m n _ _ _ _ W hW`. Take `⟨P, hP⟩` from `h m n (W.map e) (by`. Introduce `c hc`. Establish `hc' : W *ᵥ (fun j => e.symm (c j)) = 0`. Use function extensionality and compare the values at `i`.

Apply `e.injective` to reduce the goal to its premises. Use `congrFun hc i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]`. Establish `h0` using `hW _ hc'`. Use function extensionality and compare the values at `j`.

Use `congrFun h0 j` as an intermediate fact. Simplify using `using this)`. Use `⟨P.map e.symm, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply `e.injective` to reduce the goal to its premises.

Use `congrFun (congrFun hP i) j` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.map_apply] at this`. Rewrite using `[Matrix.mul_apply, map_sum]`. Simplify using `only [map_mul, Matrix.map_apply, RingEquiv.apply_symm_apply]`. Rewrite using `[this]`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
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
Use `letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _`. Use `letI : ∀ m : MaximalSpectrum R, Field (R ⧸ m.asIdeal) := fun m => Ideal.Quotient.field m.asIdeal`. Conclude with `lip_of_ringEquiv (IsArtinianRing.equivPi R) (PI.VolStabS.TensAllW.lip_pi (fun m : MaximalSpectrum R => R ⧸ m.asIdeal) (fun m => PI.VolStabS.TensAllW.lip_field _))`.
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
Introduce `F E _ _ _ _ _ σ _ R _ _ _ _ _ hR n M`. Take `⟨hT, -, -, -, hA, hRed, hU, -⟩` from `hR`. Use `haveI := hT`. Use `haveI := hA`. Use `haveI := hRed`.

Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hUo : IsOpen {r : R | IsUnit r}`. Use `hU.isOpen_range` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `r`.

Simplify using `[IsUnit]`. Conclude with `PI.VolStabS.TensAllW.isOpen_linIndep (Module.finBasis F E) R hUo (lip_of_artinian_reduced R)`.
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
