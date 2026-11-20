import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselAdjoint

/- English proof (translation)
Distinguish the cases in `hf : AEStronglyMeasurable f μ`. Establish `h1 : AEStronglyMeasurable f (μ.map T)` using `by rw [hT.map_eq]; exact hf`. Rewrite using `[← integral_map hT.measurable.aemeasurable h1, hT.map_eq]`. Establish `hg : ¬ AEStronglyMeasurable (fun p => f (T p)) μ`. Introduce `hg`.

Apply `hf` to reduce the goal to its premises. Use `(hg.comp_measurePreserving hT).congr ?_` and prove the remaining obligations. Use `filter_upwards [hTT] with p hp`. Simplify using `[hp]`. Rewrite using `[integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hg]`.
-/
theorem integral_comp_involution {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ) (hTT : ∀ᵐ p ∂μ, T (T p) = p) (f : X → E) :
    ∫ p, f (T p) ∂μ = ∫ p, f p ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have h1 : AEStronglyMeasurable f (μ.map T) := by rw [hT.map_eq]; exact hf
    rw [← integral_map hT.measurable.aemeasurable h1, hT.map_eq]
  · have hg : ¬ AEStronglyMeasurable (fun p => f (T p)) μ := by
      intro hg
      apply hf
      refine (hg.comp_measurePreserving hT).congr ?_
      filter_upwards [hTT] with p hp
      simp [hp]
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hg]

def adjR (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] :
    (W →L[ℂ] W) →ₗᵢ[ℝ] (W →L[ℂ] W) where
  toFun A := ContinuousLinearMap.adjoint A
  map_add' A B := map_add _ A B
  map_smul' c A := by
    have e : ∀ B : W →L[ℂ] W, c • B = (c : ℂ) • B := fun B => by
      ext x; simp
    rw [RingHom.id_apply, e, e, map_smulₛₗ]; simp
  norm_map' A := ContinuousLinearMap.adjoint.norm_map A

/- English proof (translation)
The claim follows from `((adjR W).integral_comp_comm f).symm`.
-/
theorem adjoint_integral {X W : Type*} [MeasurableSpace X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (μ : Measure X) (f : X → (W →L[ℂ] W)) :
    ContinuousLinearMap.adjoint (∫ p, f p ∂μ) = ∫ p, ContinuousLinearMap.adjoint (f p) ∂μ :=
  ((adjR W).integral_comp_comm f).symm

/- English proof (translation)
Introduce `_ k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS _ hOK hS v _ w _`. Take `⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩` from `hS`. Take `⟨-, hinv, -, -, -, hae⟩` from `GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hOK.1 hz hT hW hN`. Take `⟨-, -, hψi, hψc, hUW, hNG⟩` from `GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz`. Unfold `be`.

Rewrite using `[adjoint_integral, ← integral_comp_involution hinv ?_ (beInt z Formalism.QuantumDeterminants.cStd π R.σ v w)]`. Use `integral_congr_ae ?_ filter_upwards [hae] with p hp` and prove the remaining obligations. Take `⟨hp1, hp2⟩` from `hp`. Take `⟨hi, hhi, hih⟩` from `P.MatrixMultiplicationContinuity.uw_inv hp1`. Establish `hg1 : Matrix.of p.1 ∈ GG k r` using `hp1.1`.

Establish `hg2 : Matrix.of p.2 ∈ GG k r` using `hp2.1`. Establish `hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r`. Establish `a1 : (Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1 = Formalism.QuantumDeterminants.Hpk k r` using `hg1`. Establish `a2 : (Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.2 = Formalism.QuantumDeterminants.Hpk k r` using `hg2`. Use `show (Matrix.of p.1 * Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p.1 * Matrix.of p.2) = Formalism.QuantumDeterminants.Hpk k r`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [a1, a2]`. Establish `hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r)` using `Matrix.inv_eq_left_inv hhi`. Establish `e1 : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) = ((Matrix.of p.1 * Matrix.of p.2)⁻¹ : Mx k r)`.

Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih, Matrix.one_mul]`. Establish `e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) = star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2))`. Rewrite using `[(hψc _ hp1 _ (hψi _ hp2).1).2.2.1, (hψi _ hp2).2]`. Establish `e3 : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π (Matrix.of p.1)`. Use `symm`.

Rewrite using `[ContinuousLinearMap.eq_adjoint_iff]`. Introduce `x y`. Rewrite using `[P.MatrixMultiplicationContinuity.piW_inner hT hπ hi, hii]`. Use `show ContinuousLinearMap.adjoint ((⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) = (⟪w, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix …`. Rewrite using `[e1, e2, hii, map_smulₛₗ, e3, P.MatrixMultiplicationContinuity.sigma_inner hDS.2 hg v w, map_mul, inner_conj_symm]`.

Both sides reduce to the same expression. Use `filter_upwards [hae] with p hp`. Take `⟨hp1, hp2⟩` from `hp`. Take `⟨hi, hhi, hih⟩` from `P.MatrixMultiplicationContinuity.uw_inv hp1`. Take `⟨-, hni, hin⟩` from `P.MatrixMultiplicationContinuity.uh_inv hp2.1`.

Establish `hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r)` using `Matrix.inv_eq_left_inv hhi`. Establish `hnn : ((Matrix.of p.2)⁻¹)⁻¹ = (Matrix.of p.2 : Mx k r)` using `Matrix.inv_eq_left_inv hni`. Establish `e : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)⁻¹ * ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.2 : Mx k r)`. Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, hii, hnn, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih, Matrix.one_mul, Matrix.mul_assoc, hih, Matrix.mul_one]`. Conclude with `Prod.ext hii e`.
-/
theorem adjoint_be : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  intro _ k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS _ hOK hS v _ w _
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨-, hinv, -, -, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hOK.1 hz hT hW hN
  obtain ⟨-, -, hψi, hψc, hUW, hNG⟩ := GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  unfold be
  rw [adjoint_integral, ← integral_comp_involution hinv ?_ (beInt z Formalism.QuantumDeterminants.cStd π R.σ v w)]
  · refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    have hg1 : Matrix.of p.1 ∈ GG k r := hp1.1
    have hg2 : Matrix.of p.2 ∈ GG k r := hp2.1
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := by
      have a1 : (Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1 = Formalism.QuantumDeterminants.Hpk k r := hg1
      have a2 : (Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.2 = Formalism.QuantumDeterminants.Hpk k r := hg2
      show (Matrix.of p.1 * Matrix.of p.2)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Matrix.of p.1 * Matrix.of p.2) = Formalism.QuantumDeterminants.Hpk k r
      calc _ = (Matrix.of p.2)ᴴ * ((Matrix.of p.1)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of p.1) * Matrix.of p.2 := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1, a2]
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have e1 : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        ((Matrix.of p.1 * Matrix.of p.2)⁻¹ : Mx k r) := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih, Matrix.one_mul]
    have e2 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2)) := by
      rw [(hψc _ hp1 _ (hψi _ hp2).1).2.2.1, (hψi _ hp2).2]
    have e3 : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π (Matrix.of p.1) := by
      symm
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [P.MatrixMultiplicationContinuity.piW_inner hT hπ hi, hii]
    show ContinuousLinearMap.adjoint ((⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) =
      (⟪w, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)) v⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹))) •
        π ((Matrix.of p.1)⁻¹)⁻¹
    rw [e1, e2, hii, map_smulₛₗ, e3, P.MatrixMultiplicationContinuity.sigma_inner hDS.2 hg v w, map_mul, inner_conj_symm]
    rfl
  · filter_upwards [hae] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hi, hhi, hih⟩ := P.MatrixMultiplicationContinuity.uw_inv hp1
    obtain ⟨-, hni, hin⟩ := P.MatrixMultiplicationContinuity.uh_inv hp2.1
    have hii : ((Matrix.of p.1)⁻¹)⁻¹ = (Matrix.of p.1 : Mx k r) := Matrix.inv_eq_left_inv hhi
    have hnn : ((Matrix.of p.2)⁻¹)⁻¹ = (Matrix.of p.2 : Mx k r) := Matrix.inv_eq_left_inv hni
    have e : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)⁻¹ * ((Matrix.of p.1)⁻¹)⁻¹ =
        (Matrix.of p.2 : Mx k r) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hii, hnn, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hih,
        Matrix.one_mul, Matrix.mul_assoc, hih, Matrix.mul_one]
    exact Prod.ext hii e

end GlobalTheory.BesselAdjoint
