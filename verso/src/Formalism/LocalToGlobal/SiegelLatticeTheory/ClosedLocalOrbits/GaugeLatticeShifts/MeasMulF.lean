import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UMatInvMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {k r : ℕ}

def mulF (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

/- English proof (translation)
The claim follows from `Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_mulP`.
-/
theorem meas_mulF : Measurable (mulF (k := k) (r := r)) :=
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_mulP

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem muS_eq (μW μN : Measure (Mt k r)) : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map mulF := rfl

/- English proof (translation)
Establish `sW` using `Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hW`. Establish `sN` using `Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hN`. Establish `hinvm : Measurable (Formalism.FourierDecayAlt.B2.invM : Mt k r → Mt k r)` using `Formalism.FourierDecayAlt.P.B2x2.invM_meas`. Establish `hWi : μW.map Formalism.FourierDecayAlt.B2.invM = μW` using `Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW`. Establish `hNi : μN.map Formalism.FourierDecayAlt.B2.invM = μN` using `Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) μN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN`.

Establish `hNc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN` using `Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN`. Set `g : Mt k r → Mt k r → Mt k r` to `fun h n => mulF (mulF (h, Formalism.FourierDecayAlt.B2.invM n), Formalism.FourierDecayAlt.B2.invM h)`. Establish `hgm : Measurable (Function.uncurry g)` using `meas_mulF.comp ((meas_mulF.comp (measurable_fst.prodMk (hinvm.comp measurable_snd))).prodMk (hinvm.comp measurable_fst))`. Establish `hW0 : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z` using `by rw [ae_iff]; exact hW.conc`. Establish `hg : ∀ᵐ h ∂μW, μN.map (g h) = μN` using `by filter_upwards [hW0] with h hh`.

Establish `e : g h = conjM (Matrix.of h) ∘ Formalism.FourierDecayAlt.B2.invM` using `rfl`. Rewrite using `[e, ← Measure.map_map (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_conj _) hinvm, hNi, hNc _ hh]`. Establish `hmp : MeasurePreserving (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) (μW.prod μN) (μW.prod μN)` using `MeasurePreserving.skew_product (μb := μW) (μd := μN) ⟨hinvm, hWi⟩ hgm hg`. Establish `hFm : Measurable (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2))` using `(hinvm.comp measurable_fst).prodMk hgm`. Establish `hae : (Formalism.FourierDecayAlt.B2.invM ∘ mulF) =ᵐ[μW.prod μN] (mulF ∘ fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2))`.

Establish `h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z`. Rewrite using `[ae_iff]`. Establish `es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} = {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ`. Use extensionality with `p`. Simplify using the standard rewrite rules.

Rewrite using `[es, Measure.prod_prod]`. Establish `: μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0` using `hW.conc`. Rewrite using `[this, zero_mul]`. Use `filter_upwards [h1] with p hp`. Establish `hu : IsUnit (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det` using `Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.det_unit_of_UH hp.1`.

Establish `hii : (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of p.1 = 1` using `Matrix.nonsing_inv_mul _ hu`. Use `show ((Matrix.of p.1 * Matrix.of p.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hii, Matrix.one_mul]`. Rewrite using `[muS_eq, Measure.map_map hinvm meas_mulF, Measure.map_congr hae, ← Measure.map_map meas_mulF hFm, hmp.map_eq]`.
-/
theorem muS_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW μN : Measure (Mt k r)}
    (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW) (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    (Formalism.MainNotions.S.muS μW μN).map Formalism.FourierDecayAlt.B2.invM = Formalism.MainNotions.S.muS μW μN := by
  have sW := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hW
  have sN := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hN
  have hinvm : Measurable (Formalism.FourierDecayAlt.B2.invM : Mt k r → Mt k r) := Formalism.FourierDecayAlt.P.B2x2.invM_meas
  have hWi : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hNi : μN.map Formalism.FourierDecayAlt.B2.invM = μN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) μN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hNc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN

  let g : Mt k r → Mt k r → Mt k r := fun h n => mulF (mulF (h, Formalism.FourierDecayAlt.B2.invM n), Formalism.FourierDecayAlt.B2.invM h)
  have hgm : Measurable (Function.uncurry g) :=
    meas_mulF.comp ((meas_mulF.comp (measurable_fst.prodMk (hinvm.comp measurable_snd))).prodMk
      (hinvm.comp measurable_fst))
  have hW0 : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.conc
  have hg : ∀ᵐ h ∂μW, μN.map (g h) = μN := by
    filter_upwards [hW0] with h hh
    have e : g h = conjM (Matrix.of h) ∘ Formalism.FourierDecayAlt.B2.invM := rfl
    rw [e, ← Measure.map_map (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_conj _) hinvm, hNi, hNc _ hh]
  have hmp : MeasurePreserving (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2))
      (μW.prod μN) (μW.prod μN) :=
    MeasurePreserving.skew_product (μb := μW) (μd := μN) ⟨hinvm, hWi⟩ hgm hg
  have hFm : Measurable (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) :=
    (hinvm.comp measurable_fst).prodMk hgm
  have hae : (Formalism.FourierDecayAlt.B2.invM ∘ mulF) =ᵐ[μW.prod μN]
      (mulF ∘ fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
      rw [ae_iff]
      have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
          {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
        ext p; simp
      rw [es, Measure.prod_prod]
      have : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0 := hW.conc
      rw [this, zero_mul]
    filter_upwards [h1] with p hp
    have hu : IsUnit (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det :=
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.det_unit_of_UH hp.1
    have hii : (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of p.1 = 1 :=
      Matrix.nonsing_inv_mul _ hu
    show ((Matrix.of p.1 * Matrix.of p.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hii, Matrix.one_mul]
  rw [muS_eq, Measure.map_map hinvm meas_mulF, Measure.map_congr hae, ← Measure.map_map meas_mulF hFm, hmp.map_eq]

end Formalism.L2.SG.RealObj.EnergyConvJ
