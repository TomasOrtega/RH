import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ hψ μK hμ c hc b`. Take `⟨-, -, hnd, -, -, -, -, -, -, hO, hC, R, hR⟩` from `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`. Set `M : AddSubgroup A.K` to `R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)`. Establish `hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK}`. Use extensionality with `z`.

Simplify using `[M, ← hR]`. Establish `hMO : IsOpen (M : Set A.K)`. Rewrite using `[hM]`. Conclude with `hO.preimage (continuous_const_smul c)`. Establish `hMC : IsCompact (M : Set A.K)`.

Rewrite using `[hM]`. Conclude with `(Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).mpr hC`. Establish `key` using `((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hμ).1 M hMO hMC).2 b`. Establish `hpsi : ∀ z y : A.K, A.psiK ψ (z * y) = ψ (Algebra.traceForm F A.K z y)`. Introduce `z y`.

Simplify using `[Et.psiK, Algebra.traceForm_apply]`. Repeatedly rewrite using `[hpsi]`. Rewrite using `[← hM]`. Use `key using 2` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Simplify using `only [Set.mem_setOf_eq, Algebra.traceForm_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Conclude with `h x (by simpa [hM] using (show x ∈ (M : Set A.K) from hx))`. Introduce `h z hz`.

Conclude with `h z (show z ∈ (M : Set A.K) by rw [hM]; exact hz)`.
-/
theorem charIntegral_inv_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ c : F, c ≠ 0 → ∀ b : A.K, ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * b) ∂μK = Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => ((μK {z : A.K | c • z ∈ A.OK}).toReal : ℂ)) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ c hc b
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hO, hC, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    simp [M, ← hR]
  have hMO : IsOpen (M : Set A.K) := by
    rw [hM]
    exact hO.preimage (continuous_const_smul c)
  have hMC : IsCompact (M : Set A.K) := by
    rw [hM]
    exact (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).mpr hC
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hμ).1
    M hMO hMC).2 b
  have hpsi : ∀ z y : A.K, A.psiK ψ (z * y) = ψ (Algebra.traceForm F A.K z y) := by
    intro z y
    simp [Et.psiK, Algebra.traceForm_apply]
  simp_rw [hpsi]
  rw [← hM]
  convert key using 2
  ext y
  simp only [Set.mem_setOf_eq, Algebra.traceForm_apply]
  constructor
  · intro h x hx
    exact h x (by simpa [hM] using (show x ∈ (M : Set A.K) from hx))
  · intro h z hz
    exact h z (show z ∈ (M : Set A.K) by rw [hM]; exact hz)

end GlobalTheory.JR
