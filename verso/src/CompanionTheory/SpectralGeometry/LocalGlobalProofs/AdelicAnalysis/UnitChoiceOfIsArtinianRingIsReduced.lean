import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Introduce `R _ _ _ k f hf`. Set `φ` to `IsArtinianRing.equivPi R`. Establish `hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0`. Introduce `I`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_exists, ne_eq, not_not] at h`. Use `haveI : I.asIdeal.IsMaximal := I.isMaximal`. Set `ψ : R →+* R ⧸ I.asIdeal` to `(Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom`. Establish `hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(RingHom.mem_ker).2 (h i)`. Rewrite `hle` using `[hf]`. Establish `h1 : ψ 1 = 0` using `(RingHom.mem_ker).1 (hle Submodule.mem_top)`. Rewrite `h1` using `[map_one]`.

Conclude with `one_ne_zero h1`. Use `choose c hc using hex`. Set `E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal` to `fun i I => if c I = i then 1 else 0`. Use `⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Rewrite using `[← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `I`. Simplify using `only [E, Pi.mul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `i j hij`. Rewrite using `[← map_mul, ← map_zero φ.symm]`. Use `congr 1`. Use function extensionality and compare the values at `I`. Simplify using `only [E, Pi.mul_apply, Pi.zero_apply]`.

Apply the tactic sequence `split_ifs with h1 h2 <;> simp_all`. Rewrite using `[← map_sum, ← map_one φ.symm]`. Use `congr 1`. Use function extensionality and compare the values at `I`. Simplify using `only [E, Finset.sum_apply, Pi.one_apply]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Rewrite using `[← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]`. Introduce `I`. Establish `hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I`.

Simplify using `only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Rewrite using `[hcomp]`. Use `haveI : I.asIdeal.IsMaximal := I.isMaximal`.

Use `letI := Ideal.Quotient.field I.asIdeal`. Conclude with `isUnit_iff_ne_zero.2 (hc I)`.
-/
theorem unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by
  intro R _ _ _ k f hf
  classical
  let φ := IsArtinianRing.equivPi R
  have hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0 := by
    intro I
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    let ψ : R →+* R ⧸ I.asIdeal :=
      (Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).2 (h i)
    rw [hf] at hle
    have h1 : ψ 1 = 0 := (RingHom.mem_ker).1 (hle Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  let E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun i I => if c I = i then 1 else 0
  refine ⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_mul]
    congr 1
    funext I
    simp only [E, Pi.mul_apply]
    split_ifs <;> simp
  · intro i j hij
    rw [← map_mul, ← map_zero φ.symm]
    congr 1
    funext I
    simp only [E, Pi.mul_apply, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all
  · rw [← map_sum, ← map_one φ.symm]
    congr 1
    funext I
    simp only [E, Finset.sum_apply, Pi.one_apply]
    rw [Finset.sum_ite_eq]
    simp
  · rw [← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]
    intro I
    have hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I := by
      simp only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul,
        one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    rw [hcomp]
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact isUnit_iff_ne_zero.2 (hc I)

end GlobalTheory.CompanionTheory.SW
