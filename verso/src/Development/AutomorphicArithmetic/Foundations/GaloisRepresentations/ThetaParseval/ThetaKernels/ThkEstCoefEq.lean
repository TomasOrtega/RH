import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstStmt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z`. Establish `hs` using `IsUWeilPair.isUSplitting hP.weil`. Use `set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw`. Establish `e : actAB (cA σ) (g, h) w = z`. Establish `a : mat g * mat g⁻¹ = 1` using `Units.mul_inv g.1`.

Establish `b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]`. Express the relevant statement in the definitionally equal form `mat g * w * (mat h)ᵀ = z`. Rewrite using `[hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b, Matrix.mul_one]`. Establish `i` using `hs.impl (g, h) w Φ₁ h₁`.

Rewrite `i` using `[e]`. Establish `k` using `inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _) (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂`. Rewrite `k` using `[i]`. Conclude with `k`.
-/
theorem coefEq_of_k : _root_.PositivityTheory.ThKEst.CoefEq_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z
  have hs := IsUWeilPair.isUSplitting hP.weil
  set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw
  have e : actAB (cA σ) (g, h) w = z := by
    have a : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1
    have b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]
    change mat g * w * (mat h)ᵀ = z
    rw [hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b,
      Matrix.mul_one]
  have i := hs.impl (g, h) w Φ₁ h₁
  rw [e] at i
  have k := inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _)
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂
  rw [i] at k
  exact k
end PositivityTheory.ThKEst
end
end
