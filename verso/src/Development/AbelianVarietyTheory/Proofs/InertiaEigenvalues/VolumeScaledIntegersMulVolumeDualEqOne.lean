import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.LatVol

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `h : ∀ᶠ y in 𝓝 x, ψ y = ψ x` using `by filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy`. Establish `h1 : ψ (y - x) = 1` using `hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(continuousAt_const).congr (h.mono fun y hy => hy.symm)`.
-/
theorem stdChar_continuous {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ y in 𝓝 x, ψ y = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)
    calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
      _ = ψ x * ψ (y - x) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ x := by rw [h1, mul_one]
  exact (continuousAt_const).congr (h.mono fun y hy => hy.symm)

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ hψ μK hsd c hc`. Take `⟨-, -, hnd, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩` from `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`. Establish `hψc` using `stdChar_continuous ψ hψ`. Establish `hcl : IsClosed {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}`. Establish `: {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} = ⋂ x : A.K, ⋂ (_ : c • x ∈ A.OK), {y : A.K | ψ (Algebra.trace F A.K (x * y)) = 1}`.

Use extensionality with `y`. Simplify using `[Et.psiK]`. Rewrite using `[this]`. Use `isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Establish `htr : Continuous (Algebra.trace F A.K)` using `IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)`.

Conclude with `hψc.comp (htr.comp (continuous_const.mul continuous_id))`. Use `⟨hcl.measurableSet, ?_⟩` and prove the remaining obligations. Set `M : AddSubgroup A.K` to `R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)`. Establish `hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK}`. Use extensionality with `z`.

Simplify using `[M, ← hR]`. Establish `hsm : Continuous fun z : A.K => c • z` using `continuous_const_smul c`. Establish `hMo : IsOpen (M : Set A.K)` using `by rw [hM]; exact hOpen.preimage hsm`. Establish `hMc : IsCompact (M : Set A.K)`. Establish `: (M : Set A.K) = (fun w : A.K => c⁻¹ • w) '' A.OK`.

Rewrite using `[hM]`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `⟨c • z, hz, inv_smul_smul₀ hc z⟩`.

Introduce and unpack `⟨w, hw, rfl⟩`. Simplify `hw` using `[smul_inv_smul₀ hc]`. Rewrite using `[this]`. Conclude with `hCpt.image (continuous_const_smul _)`. Establish `hk : (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) = A.kerK ψ`.

Use function extensionality and compare the values at `x y`. Simplify using `[Et.kerK, Et.psiK, Algebra.traceForm_apply]`. Establish `hsd' : SelfDual μK (fun x y : A.K => ψ (Algebra.traceForm F A.K x y))` using `by rw [hk]; exact hsd`. Establish `key` using `((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hsd.1).1 M hMo hMc).1.1 hsd'`. Establish `hN : {y : A.K | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} = {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}`.

Use extensionality with `y`. Simplify using `[M, ← hR, Et.psiK, Algebra.traceForm_apply]`. Rewrite `key` using `[hN, show ((M : Set A.K)) = {z : A.K | c • z ∈ A.OK} from hM]`. Establish `h1 : (μK {z : A.K | c • z ∈ A.OK}).toReal * (μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal = 1`. Rewrite using `[← ENNReal.toReal_mul, key, ENNReal.toReal_one]`.

Rewrite using `[← Complex.ofReal_mul, h1, Complex.ofReal_one]`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd c hc
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hψc := stdChar_continuous ψ hψ

  have hcl : IsClosed {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    have : {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} =
        ⋂ x : A.K, ⋂ (_ : c • x ∈ A.OK), {y : A.K | ψ (Algebra.trace F A.K (x * y)) = 1} := by
      ext y; simp [Et.psiK]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψc.comp (htr.comp (continuous_const.mul continuous_id))
  refine ⟨hcl.measurableSet, ?_⟩

  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z; simp [M, ← hR]
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMo : IsOpen (M : Set A.K) := by rw [hM]; exact hOpen.preimage hsm
  have hMc : IsCompact (M : Set A.K) := by
    have : (M : Set A.K) = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      rw [hM]; ext z; constructor
      · intro hz; exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_inv_smul₀ hc] using hw
    rw [this]; exact hCpt.image (continuous_const_smul _)
  have hk : (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) = A.kerK ψ := by
    funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
  have hsd' : SelfDual μK (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) := by rw [hk]; exact hsd
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hsd.1).1
    M hMo hMc).1.1 hsd'
  have hN : {y : A.K | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} =
      {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    ext y; simp [M, ← hR, Et.psiK, Algebra.traceForm_apply]
  rw [hN, show ((M : Set A.K)) = {z : A.K | c • z ∈ A.OK} from hM] at key
  have h1 : (μK {z : A.K | c • z ∈ A.OK}).toReal * (μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal = 1 := by
    rw [← ENNReal.toReal_mul, key, ENNReal.toReal_one]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one]

end GlobalTheory.LatVol
