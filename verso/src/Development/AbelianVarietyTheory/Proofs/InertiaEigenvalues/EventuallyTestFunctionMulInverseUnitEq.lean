import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `: CompleteSpace R` using `FiniteDimensional.complete F R`. Use `⟨Units.isOpen.mem_nhds isUnit_one, ?_⟩` and prove the remaining obligations. Establish `h` using `(NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto`. Simplify using `using h`.
-/
theorem eventually_isUnit_and_tendsto_inverse_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [NormedCommRing R] [NormedAlgebra F R] [Module.Finite F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  have : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨Units.isOpen.mem_nhds isUnit_one, ?_⟩
  have h := (NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto
  simpa using h

/- English proof (translation)
Establish `hτ : τ = moduleTopology F R` using `eq_moduleTopology F R`. Set `b` to `Module.finBasis F R`. Set `: NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F)` to `Matrix.linftyOpNormedRing`. Set `: NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F)` to `Matrix.linftyOpNormedAlgebra`. Set `N : NormedCommRing R` to `NormedCommRing.induced R _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)`.

Set `A : @NormedAlgebra F R _ N.toNormedRing.toSeminormedRing` to `NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)`. Establish `key` using `@eventually_isUnit_and_tendsto_inverse_normed F _ _ R N A ‹_›`. Establish `hN : N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = moduleTopology F R` using `@finiteNormedAlgebra_eq_moduleTopology F _ _ R N A ‹_›`. Rewrite using `[hτ, ← hN]`. Conclude with `key`.
-/
theorem eventually_isUnit_and_tendsto_inverse (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  classical
  have hτ : τ = moduleTopology F R := eq_moduleTopology F R
  let b := Module.finBasis F R
  let : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing R := NormedCommRing.induced R _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F R _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := @eventually_isUnit_and_tendsto_inverse_normed F _ _ R N A ‹_›
  have hN : N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R :=
    @finiteNormedAlgebra_eq_moduleTopology F _ _ R N A ‹_›
  rw [hτ, ← hN]
  exact key

/- English proof (translation)
Introduce `F E _ _ _ _ hU A φ' hφ a ha`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : CompleteSpace F := inferInstance`. Take `⟨hunit, hinv⟩` from `eventually_isUnit_and_tendsto_inverse F A.K`.

Establish `hC : IsCompact (tsupport φ')` using `hφ.2`. Establish `H1 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q ∈ tsupport φ', φ' (q.1 * w, q.2) = φ' q`. Use `hC.eventually_forall_of_forall_eventually fun p _ => ?_` and prove the remaining obligations. Establish `hc : Tendsto (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) (𝓝 (1, p)) (𝓝 p)`. Establish `: Continuous (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2))` using `by fun_prop`.

Simplify using `using this.tendsto (1, p)`. Establish `hl : ∀ᶠ q in 𝓝 p, φ' q = φ' p` using `hφ.1.eventually_eq p`. Establish `h2 : Tendsto (fun z : A.K × (A.K × A.K) => z.2) (𝓝 (1, p)) (𝓝 p)` using `continuous_snd.tendsto _`. Use `filter_upwards [hc.eventually hl, h2.eventually hl] with z hz1 hz2`. Conclude with `hz1.trans hz2.symm`.

Establish `H2 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q : A.K × A.K, φ' (q.1 * w, q.2) = φ' q` using `by filter_upwards [hunit, hinv.eventually H1, H1] with w hw hw' h1 q`. Distinguish the cases in `hq : q ∈ tsupport φ'`. Conclude with `h1 q hq`. Distinguish the cases in `hq' : (q.1 * w, q.2) ∈ tsupport φ'`. Use `hw' _ hq'` as an intermediate fact.

Simplify using `only [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one] at this`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hq, image_eq_zero_of_notMem_tsupport hq']`. Establish `hT : Tendsto (fun s : A.K => Ring.inverse a * s) (𝓝 a) (𝓝 1)`. Establish `: Continuous (fun s : A.K => Ring.inverse a * s)` using `by fun_prop`.

Simplify `this.tendsto a` using `[Ring.inverse_mul_cancel a ha]`. Use `filter_upwards [hT.eventually H2] with s hs t _`. Use `hs (a * Ring.inverse t, t)` as an intermediate fact. Establish `e : a * Ring.inverse t * (Ring.inverse a * s) = s * Ring.inverse t`. Combine the equalities or inequalities in the displayed calculation.

Simplify `this` using `[e]`.
-/
theorem eventually_testFn_mul_inverse_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  intro F E _ _ _ _ hU A φ' hφ a ha
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : CompleteSpace F := inferInstance
  obtain ⟨hunit, hinv⟩ := eventually_isUnit_and_tendsto_inverse F A.K
  have hC : IsCompact (tsupport φ') := hφ.2
  have H1 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q ∈ tsupport φ', φ' (q.1 * w, q.2) = φ' q := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    have hc : Tendsto (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) (𝓝 (1, p)) (𝓝 p) := by
      have : Continuous (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) := by fun_prop
      simpa using this.tendsto (1, p)
    have hl : ∀ᶠ q in 𝓝 p, φ' q = φ' p := hφ.1.eventually_eq p
    have h2 : Tendsto (fun z : A.K × (A.K × A.K) => z.2) (𝓝 (1, p)) (𝓝 p) := continuous_snd.tendsto _
    filter_upwards [hc.eventually hl, h2.eventually hl] with z hz1 hz2
    exact hz1.trans hz2.symm
  have H2 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q : A.K × A.K, φ' (q.1 * w, q.2) = φ' q := by
    filter_upwards [hunit, hinv.eventually H1, H1] with w hw hw' h1 q
    by_cases hq : q ∈ tsupport φ'
    · exact h1 q hq
    by_cases hq' : (q.1 * w, q.2) ∈ tsupport φ'
    · have := hw' _ hq'
      simp only [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hq, image_eq_zero_of_notMem_tsupport hq']
  have hT : Tendsto (fun s : A.K => Ring.inverse a * s) (𝓝 a) (𝓝 1) := by
    have : Continuous (fun s : A.K => Ring.inverse a * s) := by fun_prop
    simpa [Ring.inverse_mul_cancel a ha] using this.tendsto a
  filter_upwards [hT.eventually H2] with s hs t _
  have := hs (a * Ring.inverse t, t)
  have e : a * Ring.inverse t * (Ring.inverse a * s) = s * Ring.inverse t := by
    calc a * Ring.inverse t * (Ring.inverse a * s) = (a * Ring.inverse a) * s * Ring.inverse t := by ring
      _ = s * Ring.inverse t := by rw [Ring.mul_inverse_cancel a ha, one_mul]
  simpa [e] using this

end GlobalTheory
