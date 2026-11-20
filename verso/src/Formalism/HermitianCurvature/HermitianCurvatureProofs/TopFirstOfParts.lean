import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbJConvCpt

open MeasureTheory Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def TopFirstOfParts : Prop := TL.WordStep → RadAATop → KB.DensC → KB.TopFirst

def DegTopOfParts : Prop := TL.WordStep → RadAATop → PolyTop → KB.DensC → KB.DegTop

section lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Use `show ∫ p, JF.xiP Bs p • B.rho Bs p F g ∂Bs.μSS = ∫ p, JF.xiP Bs p • B.rho Bs p F₂ g ∂Bs.μSS`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp`. Establish `hs : B.sgs p g ∈ C6.domL Bs ∅` using `⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg.1, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hg.2.1, by simp⟩`. Simplify using `only [B.rho]`.

Rewrite using `[h _ hs]`.
-/
theorem jf_congr_pos (Bs : B.RealPlaceData k r Wp Wq) {F F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ C6.domL Bs ∅, F g = F₂ g) {g : B.Mat k r} (hg : g ∈ C6.domL Bs ∅) : B.JF Bs F g = B.JF Bs F₂ g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p F g ∂Bs.μSS = ∫ p, JF.xiP Bs p • B.rho Bs p F₂ g ∂Bs.μSS
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  have hs : B.sgs p g ∈ C6.domL Bs ∅ :=
    ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg.1, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hg.2.1, by simp⟩
  simp only [B.rho]
  rw [h _ hs]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩`.
-/
theorem cpt_zero' (Bs : B.RealPlaceData k r Wp Wq) : KB.CptCoef Bs (fun _ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩

/- English proof (translation)
Take `⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩` from `h₁`. Take `⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩` from `h₂`. Use `⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩, ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩` and prove the remaining obligations. Distinguish the cases in `h0 : F₁ g = 0`. Establish `: F₂ g ≠ 0` using `fun h2 => hne (by simp [h0, h2])`.

Conclude with `(hR₂ g hg this).trans (le_max_right _ _)`. Conclude with `(hR₁ g hg h0).trans (le_max_left _ _)`. Distinguish the cases in `h0 : F₁ g = 0`. Establish `: F₂ g ≠ 0` using `fun h2 => hne (by simp [h0, h2])`. Conclude with `(min_le_right _ _).trans (hG₂ g hg this)`.

Conclude with `(min_le_left _ _).trans (hG₁ g hg h0)`.
-/
theorem cpt_add_smul' (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g + c • F₂ g) := by
  obtain ⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩ := h₁
  obtain ⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩ := h₂
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩,
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (hR₂ g hg this).trans (le_max_right _ _)
    · exact (hR₁ g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (min_le_right _ _).trans (hG₂ g hg this)
    · exact (min_le_left _ _).trans (hG₁ g hg h0)

/- English proof (translation)
Use `cpt_add_smul' Bs (1 : ℂ) h₁ h₂` as an intermediate fact. Simplify `this` using `[one_smul]`.
-/
theorem cpt_add (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g + F₂ g) := by
  have := cpt_add_smul' Bs (1 : ℂ) h₁ h₂
  simpa [one_smul] using this

/- English proof (translation)
Use `cpt_add_smul' Bs (-1 : ℂ) h₁ h₂` as an intermediate fact. Simplify `this` using `[neg_one_smul, ← sub_eq_add_neg]`.
-/
theorem cpt_sub (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g - F₂ g) := by
  have := cpt_add_smul' Bs (-1 : ℂ) h₁ h₂
  simpa [neg_one_smul, ← sub_eq_add_neg] using this

/- English proof (translation)
Use `cpt_add_smul' Bs c (cpt_zero' Bs) h` as an intermediate fact. Simplify using `using this`.
-/
theorem cpt_smul (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h : KB.CptCoef Bs F) : KB.CptCoef Bs (fun g => c • F g) := by
  have := cpt_add_smul' Bs c (cpt_zero' Bs) h
  simpa using this

/- English proof (translation)
Take `⟨c, hc⟩` from `Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV.cpt_bound Bs F hF A hA`. Use `⟨max c 0, le_max_right _ _, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hg1 : 1 ≤ B.gN g` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg`. Establish `hpos : 0 < B.gN g ^ A` using `Real.rpow_pos_of_pos (by linarith) A`. Rewrite using `[Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpos]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gN_bound (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ B.GV k r, ‖F g‖ ≤ c * B.gN g ^ (-A) := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV.cpt_bound Bs F hF A hA
  refine ⟨max c 0, le_max_right _ _, fun g hg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hpos : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) A
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := mul_comm _ _
    _ ≤ c := hc g hg
    _ ≤ max c 0 := le_max_left _ _

/- English proof (translation)
Take `⟨c₃, hc₃⟩` from `Formalism.FourierDecayAlt.P.PBE.orbJ_dom`. Use `set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef`. Take `⟨c₁, hc₁0, hb₁⟩` from `gN_bound Bs h₁ A (le_max_left _ _)`. Take `⟨c₂, hc₂0, hb₂⟩` from `gN_bound Bs h₂ A (le_max_left _ _)`. Establish `h₁₂` using `cpt_sub Bs h₁ h₂`.

Unfold `D.vecV`. Distinguish the cases in `h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q`. Simplify using `only [dif_pos h]`. Distinguish the cases in `h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ`. Simplify using `only [dif_pos h']`.

Establish `hγ` using `h'.choose_spec.1`. Establish `hZ` using `h'.choose_spec.2.1`. Establish `hGq` using `Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ`. Establish `hpos : 0 < Gf k r Bs.z Bs.z' h'.choose` using `hGq ▸ h.2`. Take `⟨hmono, hd⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1`.

Establish `hrel` using `Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ`. Establish `horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs` using `fun p hp => ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩`. Establish `hZm` using `hZ.trans hmono`. Take `⟨θ, maj, hθ, hmaj, hdom⟩` from `hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)`. Establish `hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _` using `⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩`.

Establish `hR` using `Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG`. Establish `hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF → KB.CptCoef Bs G → (∀ g ∈ B.GV k r, ‖G g‖ ≤ cF * B.gN g ^ (-A)) → D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) G = ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS ∧ Integrable (fun p => θ p • D.orbInteg …`. Introduce `G cF hcF hGc hGb`. Establish `hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose G) Bs.μSS` using `Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb ((Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hGc.1).mono fun g hg => hg.1)`. Establish `hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS` using `Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm) (hdom G cF hcF fun p hp => hGb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))`.

Use `⟨?_, hi⟩` and prove the remaining obligations. Establish `hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧ Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS` using `⟨θ, hθ, hi⟩`. Unfold `D.orbJ`. Rewrite using `[dif_pos hex]`. Conclude with `Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ hex.choose_spec.2 hi`.

Take `⟨e1, i1⟩` from `hEq H₁ c₁ hc₁0 h₁ hb₁`. Take `⟨e2, i2⟩` from `hEq H₂ c₂ hc₂0 h₂ hb₂`. Take `⟨e12, -⟩` from `hEq (fun g => H₁ g - H₂ g) (c₁ + c₂) (add_nonneg hc₁0 hc₂0) h₁₂ (fun g hg => (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hb₁ g hg) (hb₂ g hg)))`. Rewrite using `[e12, e1, e2, ← integral_sub i1 i2]`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Simplify using `only [D.orbIntegrand, B.rho, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, smul_sub]`. Simplify using `only [dif_neg h', sub_zero]`. Simplify using `only [dif_neg h, sub_zero]`.
-/
theorem vecV_sub (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef Bs H₁) (h₂ : KB.CptCoef Bs H₂) :
    D.vecV Bs ν' m₀ (fun g => H₁ g - H₂ g) q = D.vecV Bs ν' m₀ H₁ q - D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  obtain ⟨c₁, hc₁0, hb₁⟩ := gN_bound Bs h₁ A (le_max_left _ _)
  obtain ⟨c₂, hc₂0, hb₂⟩ := gN_bound Bs h₂ A (le_max_left _ _)
  have h₁₂ := cpt_sub Bs h₁ h₂
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      have hZm := hZ.trans hmono
      obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
      have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
        ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
          fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
      have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
      have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF → KB.CptCoef Bs G →
          (∀ g ∈ B.GV k r, ‖G g‖ ≤ cF * B.gN g ^ (-A)) →
          D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) G =
              ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS ∧
            Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := by
        intro G cF hcF hGc hGb
        have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose G) Bs.μSS :=
          Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb ((Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hGc.1).mono fun g hg => hg.1)
        have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS :=
          Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm)
            (hdom G cF hcF fun p hp => hGb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
        refine ⟨?_, hi⟩
        have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
            Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
        unfold D.orbJ
        rw [dif_pos hex]
        exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
          hex.choose_spec.2 hi
      obtain ⟨e1, i1⟩ := hEq H₁ c₁ hc₁0 h₁ hb₁
      obtain ⟨e2, i2⟩ := hEq H₂ c₂ hc₂0 h₂ hb₂
      obtain ⟨e12, -⟩ := hEq (fun g => H₁ g - H₂ g) (c₁ + c₂) (add_nonneg hc₁0 hc₂0) h₁₂ (fun g hg =>
        (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hb₁ g hg) (hb₂ g hg)))
      rw [e12, e1, e2, ← integral_sub i1 i2]
      congr 1
      funext p
      simp only [D.orbIntegrand, B.rho, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, smul_sub]
    · simp only [dif_neg h', sub_zero]
  · simp only [dif_neg h, sub_zero]

end lin

section rad

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `h` using `(Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx).1`. Conclude with `⟨h.1, h.2.1, by simp⟩`.
-/
theorem cell_dom {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ C6.domL Bs ∅ := by
  have h := (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx).1
  exact ⟨h.1, h.2.1, by simp⟩

/- English proof (translation)
Introduce `x hx`. Rewrite using `[hΦ x hx]`. Simplify using `only [Q.resG]`. Rewrite using `[jf_congr_pos Bs h (cell_dom Bs hx)]`.
-/
theorem isRadOf_congr {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hΦ : Top.IsRadOf P Bs Φ F) (h : ∀ g ∈ C6.domL Bs ∅, F g = F₂ g) :
    Top.IsRadOf P Bs Φ F₂ := by
  intro x hx
  rw [hΦ x hx]
  simp only [Q.resG]
  rw [jf_congr_pos Bs h (cell_dom Bs hx)]

/- English proof (translation)
Introduce `x hx`. Establish `h₂'` using `cpt_smul Bs (-1 : ℂ) h₂`. Take `⟨ε₁, hε₁, hn₁⟩` from `Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₁`. Take `⟨ε₂, hε₂, hn₂⟩` from `Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₂'`. Establish `e : (fun g => F₁ g - F₂ g) = fun g => F₁ g + (-1 : ℂ) • F₂ g`.

Use function extensionality and compare the values at `g`. Rewrite using `[neg_one_smul, sub_eq_add_neg]`. Rewrite using `[e]`. Simplify using `only [Submodule.coe_sub, Pi.sub_apply]`. Rewrite using `[hΦ₁ x hx, hΦ₂ x hx]`.

Simplify using `only [Q.resG]`. Rewrite using `[Formalism.FourierDecayAlt.P.JCx2.bc_JF_add (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₁ (min_le_left ε₁ ε₂)) (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₂ (min_le_right ε₁ ε₂)) (Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx), Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul, smul …`.
-/
theorem isRadOf_sub {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {Φ₁ Φ₂ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂)
    (hΦ₁ : Top.IsRadOf P Bs Φ₁ F₁) (hΦ₂ : Top.IsRadOf P Bs Φ₂ F₂) :
    Top.IsRadOf P Bs (Φ₁ - Φ₂) (fun g => F₁ g - F₂ g) := by
  intro x hx
  have h₂' := cpt_smul Bs (-1 : ℂ) h₂
  obtain ⟨ε₁, hε₁, hn₁⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₁
  obtain ⟨ε₂, hε₂, hn₂⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₂'
  have e : (fun g => F₁ g - F₂ g) = fun g => F₁ g + (-1 : ℂ) • F₂ g := by
    funext g; rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [hΦ₁ x hx, hΦ₂ x hx]
  simp only [Q.resG]
  rw [Formalism.FourierDecayAlt.P.JCx2.bc_JF_add (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₁ (min_le_left ε₁ ε₂))
    (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₂ (min_le_right ε₁ ε₂)) (Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx),
    Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul, smul_add, neg_one_smul, smul_neg, sub_eq_add_neg]

/- English proof (translation)
Take `⟨ε, hε, hn⟩` from `Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF`. Take `⟨Φ, hΦ⟩` from `Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' p.T.base F p.hP rfl rfl rfl rfl ⟨hn.2.1, ε, hε, hn.2.2⟩`. Conclude with `⟨Φ, hΦ⟩`.
-/
theorem radExists {P : M.Par} (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) : ∃ Φ, Top.IsRadOf P p.T.base Φ F := by
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' p.T.base F
    p.hP rfl rfl rfl rfl ⟨hn.2.1, ε, hε, hn.2.2⟩
  exact ⟨Φ, hΦ⟩

/- English proof (translation)
Establish `h0` using `isRadOf_sub p.T.base h₁ h₂ hΦ₁ hΦ₂`. Rewrite `h0` using `[sub_self]`. Establish `hv` using `hDC Wp Wq P p _ (cpt_sub p.T.base h₁ h₂) h0 a`. Establish `e` using `vecV_sub p.T.base p.ν' p.m₀ a h₁ h₂`. Unfold `KB.Pl.V at hv ⊢`.

Rewrite `hv` using `[e]`. Conclude with `sub_eq_zero.1 hv`.
-/
theorem vecV_eq_of_rad (hDC : KB.DensC) {P : M.Par} (p : KB.Pl P Wp Wq) {F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef p.T.base F₁) (h₂ : KB.CptCoef p.T.base F₂) {Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'}
    (hΦ₁ : Top.IsRadOf P p.T.base Φ F₁) (hΦ₂ : Top.IsRadOf P p.T.base Φ F₂) (a : C.LPt) : p.V F₁ a = p.V F₂ a := by
  have h0 := isRadOf_sub p.T.base h₁ h₂ hΦ₁ hΦ₂
  rw [sub_self] at h0
  have hv := hDC Wp Wq P p _ (cpt_sub p.T.base h₁ h₂) h0 a
  have e := vecV_sub p.T.base p.ν' p.m₀ a h₁ h₂
  unfold KB.Pl.V at hv ⊢
  rw [e] at hv
  exact sub_eq_zero.1 hv

end rad

end Formalism.FourierDecayAlt.P.PBN
