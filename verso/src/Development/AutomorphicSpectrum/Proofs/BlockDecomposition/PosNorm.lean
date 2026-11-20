import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.PosNormFD

/- English proof (translation)
Introduce `E _ _ _ N _ _ μ _ 𝓕 h𝓕 φ hA hS hne`. Use `haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL`. Establish `hc : Continuous φ.1` using `GlobalTheory.CuspRep.IsAutForm.continuous hA`. Establish `hl` using `GlobalTheory.DiscreteUnit.left_latticeGL hA hS`. Assume the negation of the conclusion as `h0`.

Establish `h0' : ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ = 0` using `by simpa using h0`. Establish `hm : Measurable fun g => ‖φ.1 g‖ₑ ^ 2` using `hc.enorm.measurable.pow_const 2`. Establish `hz` using `(lintegral_eq_zero_iff hm).1 h0'`. Establish `hSo : IsOpen {g | φ.1 g ≠ 0}` using `isOpen_ne_fun hc continuous_const`. Establish `hSF : μ ({g | φ.1 g ≠ 0} ∩ 𝓕) = 0`.

Rewrite using `[← Measure.restrict_apply hSo.measurableSet]`. Use `measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)` and prove the remaining obligations. Establish `hg' : φ.1 g ≠ 0` using `hg`. Simplify `hg'` using `[hg']`. Establish `hinv : ∀ γ : latticeGL E N, γ • {g | φ.1 g ≠ 0} = {g | φ.1 g ≠ 0}` using `fun γ => by`.

Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Establish `e : φ.1 (γ⁻¹ • x) = φ.1 x` using `hl _ (γ⁻¹).2 x`. Simplify using `only [Set.mem_setOf_eq, e]`. Establish `hS0` using `h𝓕.measure_zero_of_invariant _ hinv hSF`.

Establish `hemp` using `(hSo.measure_eq_zero_iff μ).1 hS0`. Use `hne (Subtype.ext (funext fun g => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hg`. Conclude with `(Set.eq_empty_iff_forall_notMem.1 hemp g) hg`.
-/
theorem posNorm : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.PosNorm := by
  intro E _ _ _ N _ _ μ _ 𝓕 h𝓕 φ hA hS hne
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  have hc : Continuous φ.1 := GlobalTheory.CuspRep.IsAutForm.continuous hA
  have hl := GlobalTheory.DiscreteUnit.left_latticeGL hA hS
  by_contra h0
  have h0' : ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ = 0 := by simpa using h0
  have hm : Measurable fun g => ‖φ.1 g‖ₑ ^ 2 := hc.enorm.measurable.pow_const 2
  have hz := (lintegral_eq_zero_iff hm).1 h0'
  have hSo : IsOpen {g | φ.1 g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hSF : μ ({g | φ.1 g ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hSo.measurableSet]
    refine measure_mono_null (fun g hg => ?_) (ae_iff.1 hz)
    have hg' : φ.1 g ≠ 0 := hg
    simpa [hg'] using hg'
  have hinv : ∀ γ : latticeGL E N, γ • {g | φ.1 g ≠ 0} = {g | φ.1 g ≠ 0} := fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e : φ.1 (γ⁻¹ • x) = φ.1 x := hl _ (γ⁻¹).2 x
    simp only [Set.mem_setOf_eq, e]
  have hS0 := h𝓕.measure_zero_of_invariant _ hinv hSF
  have hemp := (hSo.measure_eq_zero_iff μ).1 hS0
  refine hne (Subtype.ext (funext fun g => ?_))
  by_contra hg
  exact (Set.eq_empty_iff_forall_notMem.1 hemp g) hg

end GlobalTheory.CompanionTheory.PosNormFD
