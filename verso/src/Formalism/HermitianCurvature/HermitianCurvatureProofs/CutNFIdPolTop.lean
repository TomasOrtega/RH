import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPol

namespace Formalism.FourierDecayAlt.P.CutBP.PolTop

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Unfold `D.orbIntegrand B.rho`. Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add, map_smul, smul_add]`. Rewrite using `[smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]`.
-/
theorem orbital_integrand_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (a b : ℂ) (p : B.SS k r) :
    D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) p =
      a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p := by

  unfold D.orbIntegrand B.rho
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]

/- English proof (translation)
Take `⟨c₃, hc₃⟩` from `Formalism.FourierDecayAlt.P.PBE.orbJ_dom`. Use `⟨c₃, ?_⟩` and prove the remaining obligations. Introduce `k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b`. Take `⟨θ, maj, hθ, hmaj, hdom⟩` from `hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA`. Establish `hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d` using `⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩`.

Establish `hR` using `Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG`. Establish `hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c → AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS → (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) → Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS` using `fun G c hc hGm hGb => Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)`. Establish `hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c → AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS → (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) → D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS`. Introduce `G c hc hGm hGb`. Establish `hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧ Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS` using `⟨θ, hθ, hInt G c hc hGm hGb⟩`.

Unfold `D.orbJ`. Rewrite using `[dif_pos hex]`. Conclude with `Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ hex.choose_spec.2 (hInt G c hc hGm hGb)`. Establish `hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) = fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p`. Use function extensionality and compare the values at `fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p`.

Establish `hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS`. Rewrite using `[hlin]`. Conclude with `(hm₁.const_smul a).add (hm₂.const_smul b)`. Establish `hc' : 0 ≤ (‖a‖ + ‖b‖) * cF` using `mul_nonneg (by positivity) hcF`. Establish `hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A)`.

Introduce `p hp`. Establish `h1` using `hb₁ p hp`. Establish `h2` using `hb₂ p hp`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul, norm_smul]`. Use `_ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) := add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))`. Use `_ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring`. Establish `i₁` using `hInt H₁ cF hcF hm₁ hb₁`. Establish `i₂` using `hInt H₂ cF hcF hm₂ hb₂`.

Rewrite using `[hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]`. Establish `e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) = fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p)`. Use function extensionality and compare the values at `p`. Rewrite using `[smul_add, smul_comm (θ p) a, smul_comm (θ p) b]`. Establish `j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS` using `i₁.smul a`.

Establish `j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS` using `i₂.smul b`. Rewrite using `[e, integral_add j₁ j₂, integral_smul, integral_smul]`.
-/
theorem orbJ_linear_of_decay : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₁) Bs.μSS →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₂) Bs.μSS →
      (∀ p, Bs.inSS p → ‖H₁ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₂ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) → ∀ a b : ℂ,
      D.orbJ Bs γ (D.muR Bs γ w) (fun g => a • H₁ g + b • H₂ g) =
        a • D.orbJ Bs γ (D.muR Bs γ w) H₁ + b • D.orbJ Bs γ (D.muR Bs γ w) H₂ := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d := ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ,
    Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G c hc hGm hGb =>
    Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)
  have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G c hc hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G c hc hGm hGb⟩
    unfold D.orbJ
    rw [dif_pos hex]
    exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G c hc hGm hGb)
  have hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) =
      fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p :=
    funext fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS := by
    rw [hlin]
    exact (hm₁.const_smul a).add (hm₂.const_smul b)
  have hc' : 0 ≤ (‖a‖ + ‖b‖) * cF := mul_nonneg (by positivity) hcF
  have hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤
      (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by
    intro p hp
    have h1 := hb₁ p hp
    have h2 := hb₂ p hp
    calc ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ ‖a‖ * ‖H₁ (B.sgs p γ)‖ + ‖b‖ * ‖H₂ (B.sgs p γ)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring
  have i₁ := hInt H₁ cF hcF hm₁ hb₁
  have i₂ := hInt H₂ cF hcF hm₂ hb₂
  rw [hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]
  have e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) =
      fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p) := by
    funext p
    rw [smul_add, smul_comm (θ p) a, smul_comm (θ p) b]
  have j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS := i₁.smul a
  have j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS := i₂.smul b
  rw [e, integral_add j₁ j₂, integral_smul, integral_smul]

/- English proof (translation)
Take `⟨c₃, hc₃⟩` from `orbJ_linear_of_decay`. Use `⟨c₃, ?_⟩` and prove the remaining obligations. Introduce `k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b`. Unfold `D.vecV`. Distinguish the cases in `h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q`.

Simplify using `only [dif_pos h]`. Distinguish the cases in `h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ`. Simplify using `only [dif_pos h']`. Establish `hγ` using `h'.choose_spec.1`. Establish `hZ` using `h'.choose_spec.2.1`.

Establish `hGq` using `Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ`. Establish `hpos : 0 < Gf k r Bs.z Bs.z' h'.choose` using `hGq ▸ h.2`. Take `⟨hmono, hd⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1`. Establish `hrel` using `Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ`. Establish `horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs` using `fun p hp => ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩`.

Conclude with `hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂) (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b`. Simplify using `only [dif_neg h']`. Simplify using the standard rewrite rules. Simplify using `only [dif_neg h]`. Simplify using the standard rewrite rules.
-/
theorem vector_valued_orbital_linear : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      ContinuousOn H₁ (B.GPos Bs) → ContinuousOn H₂ (B.GPos Bs) →
      (∀ g ∈ B.GPos Bs, ‖H₁ g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₂ g‖ ≤ cF * B.gN g ^ (-A)) →
      ∀ a b : ℂ, D.vecV Bs ν' m₀ (fun g => a • H₁ g + b • H₂ g) q =
        a • D.vecV Bs ν' m₀ H₁ q + b • D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := orbJ_linear_of_decay
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b
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
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF
        (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂)
        (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b
    · simp only [dif_neg h']
      simp
  · simp only [dif_neg h]
    simp

/- English proof (translation)
Establish `hR : ∀ w : List (B.Mat k r), B.Rw w (c • F) = c • B.Rw w F`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons X w ih => show Formalism.REAL.RdV X (B.Rw w (c • F)) = c • Formalism.REAL.RdV X (B.Rw w F)`.

Rewrite using `[ih]`. Use function extensionality and compare the values at `g`. Conclude with `deriv_const_smul' c _`. Establish `hT : ∀ T : B.DTerm k r Wp Wq, T.coef g (B.Rw T.word (c • F) g) = c • T.coef g (B.Rw T.word F g)` using `fun T => by rw [hR, Pi.smul_apply, map_smul]`. Unfold `B.opApply`.

Simplify using `only [hT]`. Proceed by induction on `Θ with`. Consider the case `nil => simp`. Consider the case `cons T Θ ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, smul_add]`.
-/
theorem opApply_smul' {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Θ : B.DiffOp k r Wp Wq) (c : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply Θ (c • F) g = c • B.opApply Θ F g := by

  have hR : ∀ w : List (B.Mat k r), B.Rw w (c • F) = c • B.Rw w F := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show Formalism.REAL.RdV X (B.Rw w (c • F)) = c • Formalism.REAL.RdV X (B.Rw w F)
      rw [ih]
      funext g
      exact deriv_const_smul' c _
  have hT : ∀ T : B.DTerm k r Wp Wq, T.coef g (B.Rw T.word (c • F) g) = c • T.coef g (B.Rw T.word F g) :=
    fun T => by rw [hR, Pi.smul_apply, map_smul]
  unfold B.opApply
  simp only [hT]
  induction Θ with
  | nil => simp
  | cons T Θ ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, smul_add]

/- English proof (translation)
Introduce `g hg`. Establish `e : (fun x => a • F₁ x + b • F₂ x) = fun x => (a • F₁) x - ((-b) • F₂) x`. Use function extensionality and compare the values at `x`. Simplify using `[neg_smul, sub_neg_eq_add]`. Rewrite using `[e, Formalism.FourierDecayAlt.P.PBE.opApply_sub Θ (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' a h₁) (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' (-b) h₂) g hg, opApply_smul', opApply_smul', neg_smul, sub_neg_eq_add]`.
-/
theorem diff_operator_apply_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Θ : B.DiffOp k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : B.CkOn ⊤ (B.GV k r) F₁) (h₂ : B.CkOn ⊤ (B.GV k r) F₂) (a b : ℂ) :
    ∀ g ∈ B.GV k r, B.opApply Θ (fun x => a • F₁ x + b • F₂ x) g =
      a • B.opApply Θ F₁ g + b • B.opApply Θ F₂ g := by
  intro g hg
  have e : (fun x => a • F₁ x + b • F₂ x) = fun x => (a • F₁) x - ((-b) • F₂) x := by
    funext x
    simp [neg_smul, sub_neg_eq_add]
  rw [e, Formalism.FourierDecayAlt.P.PBE.opApply_sub Θ (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' a h₁) (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' (-b) h₂) g hg,
    opApply_smul', opApply_smul', neg_smul, sub_neg_eq_add]

/- English proof (translation)
Take `⟨K, hK0, hKb⟩` from `Formalism.FourierDecayAlt.P.PBE.opApply_bound Bs fib hfib hIn hε₀`. Use `⟨K, hK0, fun G A' c hG hGs hG0 => ⟨?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Establish `hGPG : B.GPos Bs ⊆ B.GV k r` using `fun g hg => hg.1`. Apply `Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn` to reduce the goal to its premises. Introduce `T hT`.

Establish `h1 : ContinuousOn T.coef (B.GPos Bs)` using `(Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' (fun g hg => hg.1) (hIn.1 T hT).1).mono (fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)`. Establish `h2 : ContinuousOn (B.Rw T.word G) (B.GPos Bs)` using `(Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hGs T.word T.word_lie)).mono hGPG`. Conclude with `h1.clm_apply h2`. Establish `hGc : Continuous (fun g : B.Mat k r => Gf k r Bs.z Bs.z' g)` using `(Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous`. Establish `hopen : IsOpen {x : B.Mat k r | Gf k r Bs.z Bs.z' x < ε₀}` using `isOpen_lt hGc continuous_const`.

Establish `e : -(A' - ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o)) = (κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A'` using `by ring`. Rewrite using `[e]`. Distinguish the cases in `hgl : Gf k r Bs.z Bs.z' g < ε₀`. Rewrite using `[Formalism.FourierDecayAlt.P.PBE.opApply_zero_near Dop hopen (fun x _ hx => hG0 x hx) g hg.1 hgl, norm_zero]`. Conclude with `mul_nonneg (mul_nonneg hK0 (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hG)) (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg g) _)`.

Conclude with `hKb G A' c hG g hg.1 (not_lt.1 hgl)`.
-/
theorem op_cut_dec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Dop : B.DiffOp k r Wp Wq} (hIn : C6.InDDPlus Bs fib ∅ o κ Dop)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (A' c : ℝ), B.CCle A' o G c → B.CkOn ⊤ (B.GV k r) G →
      (∀ x, Gf k r Bs.z Bs.z' x < ε₀ → G x = 0) →
      ContinuousOn (B.opApply Dop G) (B.GPos Bs) ∧
      ∀ g ∈ B.GPos Bs, ‖B.opApply Dop G g‖ ≤ K * c * B.gN g ^ (-(A' - ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o))) := by
  obtain ⟨K, hK0, hKb⟩ := Formalism.FourierDecayAlt.P.PBE.opApply_bound Bs fib hfib hIn hε₀
  refine ⟨K, hK0, fun G A' c hG hGs hG0 => ⟨?_, fun g hg => ?_⟩⟩
  · have hGPG : B.GPos Bs ⊆ B.GV k r := fun g hg => hg.1
    apply Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
    intro T hT
    have h1 : ContinuousOn T.coef (B.GPos Bs) :=
      (Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' (fun g hg => hg.1) (hIn.1 T hT).1).mono
        (fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
    have h2 : ContinuousOn (B.Rw T.word G) (B.GPos Bs) :=
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hGs T.word T.word_lie)).mono hGPG
    exact h1.clm_apply h2
  · have hGc : Continuous (fun g : B.Mat k r => Gf k r Bs.z Bs.z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
    have hopen : IsOpen {x : B.Mat k r | Gf k r Bs.z Bs.z' x < ε₀} := isOpen_lt hGc continuous_const
    have e : -(A' - ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o)) = (κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A' := by ring
    rw [e]
    by_cases hgl : Gf k r Bs.z Bs.z' g < ε₀
    · rw [Formalism.FourierDecayAlt.P.PBE.opApply_zero_near Dop hopen (fun x _ hx => hG0 x hx) g hg.1 hgl, norm_zero]
      exact mul_nonneg (mul_nonneg hK0 (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hG))
        (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg g) _)
    · exact hKb G A' c hG g hg.1 (not_lt.1 hgl)

/- English proof (translation)
Establish `hv : B.hsVec ((1 / 2 : ℂ) • X + (1 / 2 : ℂ) • Y) = (1 / 2 : ℂ) • (B.hsVec X + B.hsVec Y)`. Unfold `B.hsVec`. Use extensionality with `i`. Simplify using `[smul_add]`. Unfold `B.hsInner`.

Rewrite using `[hv]`. Establish `e1 : ∀ u : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ u u).re = ‖u‖ ^ 2`. Introduce `u`. Simplify using `using (inner_self_eq_norm_sq (𝕜 := ℂ) u)`. Establish `hxy : (inner ℂ (B.hsVec X) (B.hsVec Y)).re = (inner ℂ (B.hsVec Y) (B.hsVec X)).re`.

Rewrite using `[← inner_conj_symm (B.hsVec X) (B.hsVec Y)]`. Conclude with `Complex.conj_re _`. Establish `hadd : ‖B.hsVec X + B.hsVec Y‖ ^ 2 = ‖B.hsVec X‖ ^ 2 + 2 * (inner ℂ (B.hsVec X) (B.hsVec Y)).re + ‖B.hsVec Y‖ ^ 2`. Simplify using `using (norm_add_sq (𝕜 := ℂ) (B.hsVec X) (B.hsVec Y))`. Rewrite using `[e1, e1, e1, norm_smul, mul_pow, hadd, hxy]`.

Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hs_mid {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X Y : Wq →L[ℂ] Wp) :
    (B.hsInner ((1 / 2 : ℂ) • X + (1 / 2 : ℂ) • Y) ((1 / 2 : ℂ) • X + (1 / 2 : ℂ) • Y)).re =
      (B.hsInner X X).re / 4 + (B.hsInner Y Y).re / 4 + (B.hsInner X Y).re / 2 := by
  have hv : B.hsVec ((1 / 2 : ℂ) • X + (1 / 2 : ℂ) • Y) = (1 / 2 : ℂ) • (B.hsVec X + B.hsVec Y) := by
    unfold B.hsVec
    ext i
    simp [smul_add]
  unfold B.hsInner
  rw [hv]
  have e1 : ∀ u : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ u u).re = ‖u‖ ^ 2 := by
    intro u
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u)
  have hxy : (inner ℂ (B.hsVec X) (B.hsVec Y)).re = (inner ℂ (B.hsVec Y) (B.hsVec X)).re := by
    rw [← inner_conj_symm (B.hsVec X) (B.hsVec Y)]
    exact Complex.conj_re _
  have hadd : ‖B.hsVec X + B.hsVec Y‖ ^ 2 =
      ‖B.hsVec X‖ ^ 2 + 2 * (inner ℂ (B.hsVec X) (B.hsVec Y)).re + ‖B.hsVec Y‖ ^ 2 := by
    simpa using (norm_add_sq (𝕜 := ℂ) (B.hsVec X) (B.hsVec Y))
  rw [e1, e1, e1, norm_smul, mul_pow, hadd, hxy]
  norm_num
  ring

/- English proof (translation)
Establish `hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1` using `by push_cast; ring`. Rewrite `ho`, the goal using `[hn]`. Use `set s : ℝ := (r : ℝ) + 1 with hs`. Use `set n : ℝ := 2 * (r : ℝ) + k + 1 with hn'`. Use `set D : ℝ := max Cb 0 with hD`.

Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hs1 : 1 ≤ s` using `by rw [hs]; linarith`. Establish `hn1 : 1 ≤ n` using `by rw [hn']; linarith`. Establish `hrn : (r : ℝ) ≤ n - 1` using `by rw [hn']; linarith`.

Establish `hD0 : 0 ≤ D` using `le_max_right _ _`. Establish `hCbD : Cb ≤ D` using `le_max_left _ _`. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `hLN : (L : ℝ) ≤ N` using `by exact_mod_cast hL`. Establish `ho0 : (0 : ℝ) ≤ o` using `Nat.cast_nonneg o`.

Establish `hL0 : (0 : ℝ) ≤ L` using `Nat.cast_nonneg L`. Establish `hn0 : 0 ≤ n` using `by linarith`. Establish `hs0 : 0 ≤ s` using `by linarith`. Establish `ho' : (o : ℝ) ≤ D * N * n`. Combine the equalities or inequalities in the displayed calculation.

Establish `hκ' : (κ : ℝ) ≤ D * D * s * N * n`. Combine the equalities or inequalities in the displayed calculation. Establish `hs4 : s ≤ s ^ 4` using `le_self_pow₀ hs1 (by norm_num)`. Establish `hs24 : s ^ 2 ≤ s ^ 4` using `pow_le_pow_right₀ hs1 (by norm_num)`. Establish `hnn : n ≤ n ^ 2` using `le_self_pow₀ hn1 (by norm_num)`.

Establish `hrn1 : (r : ℝ) * n + 1 ≤ n ^ 3`. Establish `h1 : (r : ℝ) * n ≤ (n - 1) * n` using `mul_le_mul_of_nonneg_right hrn hn0`. Establish `h2 : n ^ 2 ≤ n ^ 3` using `pow_le_pow_right₀ hn1 (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hT1 : 0 ≤ s ^ 4 * (N * n ^ 2)` using `by positivity`.

Establish `hT2 : 0 ≤ s ^ 4 * n ^ 3` using `by positivity`. Establish `hc3 : c₃ * s ^ 2 * ((r : ℝ) * n + 1) ≤ |c₃| * (s ^ 4 * n ^ 3)`. Establish `h0 : 0 ≤ s ^ 2 * ((r : ℝ) * n + 1)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hsn : s * N * n ≤ s ^ 4 * (N * n ^ 2)`.

Use `mul_le_mul hs4 (mul_le_mul_of_nonneg_left hnn hN0) (by positivity) (by positivity)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA' : |c₃| * (s ^ 4 * n ^ 3) + 5 * D * (s ^ 4 * (N * n ^ 2)) + D ^ 2 * (s ^ 4 * (N * n ^ 2)) ≤ A`. Establish `hmain : |c₃| * (s ^ 4 * n ^ 3) + 5 * D * (s ^ 4 * (N * n ^ 2)) + D ^ 2 * (s ^ 4 * (N * n ^ 2)) ≤ (|c₃| + 5 * D + D ^ 2) * s ^ 4 * (N * n ^ 2 + n ^ 3)`. Establish `h1 : 0 ≤ 5 * D * (s ^ 4 * n ^ 3)` using `by positivity`.

Establish `h2 : 0 ≤ D ^ 2 * (s ^ 4 * n ^ 3)` using `by positivity`. Establish `h3 : 0 ≤ |c₃| * (s ^ 4 * (N * n ^ 2))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : 5 * s * o ≤ 5 * D * (s ^ 4 * (N * n ^ 2))`.

Establish `: s * o ≤ s * (D * N * n)` using `mul_le_mul_of_nonneg_left ho' hs0`. Establish `: D * (s * N * n) ≤ D * (s ^ 4 * (N * n ^ 2))` using `mul_le_mul_of_nonneg_left hsn hD0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : D * D * s * N * n ≤ D ^ 2 * (s ^ 4 * (N * n ^ 2))`. Use `mul_le_mul_of_nonneg_left hsn (mul_nonneg hD0 hD0)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weight_threshold_budget_inequality (c₃ Cb A : ℝ) (r k N L o κ : ℕ) (hL : L ≤ N)
    (ho : (o : ℝ) ≤ Cb * (L : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) (hκ : (κ : ℝ) ≤ Cb * ((r : ℝ) + 1) * (o : ℝ))
    (hA : (|c₃| + 5 * max Cb 0 + max Cb 0 ^ 2) * ((r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A) :
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      A - 2 * ((r : ℝ) + 1) * o - ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o) := by
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn] at ho ⊢
  set s : ℝ := (r : ℝ) + 1 with hs
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn'
  set D : ℝ := max Cb 0 with hD
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hn1 : 1 ≤ n := by rw [hn']; linarith
  have hrn : (r : ℝ) ≤ n - 1 := by rw [hn']; linarith
  have hD0 : 0 ≤ D := le_max_right _ _
  have hCbD : Cb ≤ D := le_max_left _ _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hLN : (L : ℝ) ≤ N := by exact_mod_cast hL
  have ho0 : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := by linarith
  have ho' : (o : ℝ) ≤ D * N * n := by
    calc (o : ℝ) ≤ Cb * L * n := ho
      _ ≤ D * L * n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbD hL0) hn0
      _ ≤ D * N * n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLN hD0) hn0
  have hκ' : (κ : ℝ) ≤ D * D * s * N * n := by
    calc (κ : ℝ) ≤ Cb * s * o := hκ
      _ ≤ D * s * o := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbD hs0) ho0
      _ ≤ D * s * (D * N * n) := mul_le_mul_of_nonneg_left ho' (mul_nonneg hD0 hs0)
      _ = D * D * s * N * n := by ring
  have hs4 : s ≤ s ^ 4 := le_self_pow₀ hs1 (by norm_num)
  have hs24 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hnn : n ≤ n ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have hrn1 : (r : ℝ) * n + 1 ≤ n ^ 3 := by
    have h1 : (r : ℝ) * n ≤ (n - 1) * n := mul_le_mul_of_nonneg_right hrn hn0
    have h2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    nlinarith
  have hT1 : 0 ≤ s ^ 4 * (N * n ^ 2) := by positivity
  have hT2 : 0 ≤ s ^ 4 * n ^ 3 := by positivity
  have hc3 : c₃ * s ^ 2 * ((r : ℝ) * n + 1) ≤ |c₃| * (s ^ 4 * n ^ 3) := by
    have h0 : 0 ≤ s ^ 2 * ((r : ℝ) * n + 1) := by positivity
    calc c₃ * s ^ 2 * ((r : ℝ) * n + 1) = c₃ * (s ^ 2 * ((r : ℝ) * n + 1)) := by ring
      _ ≤ |c₃| * (s ^ 2 * ((r : ℝ) * n + 1)) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |c₃| * (s ^ 4 * n ^ 3) := mul_le_mul_of_nonneg_left (mul_le_mul hs24 hrn1 (by positivity) (by positivity)) (abs_nonneg _)
  have hsn : s * N * n ≤ s ^ 4 * (N * n ^ 2) := by
    have := mul_le_mul hs4 (mul_le_mul_of_nonneg_left hnn hN0) (by positivity) (by positivity)
    linarith
  have hA' : |c₃| * (s ^ 4 * n ^ 3) + 5 * D * (s ^ 4 * (N * n ^ 2)) + D ^ 2 * (s ^ 4 * (N * n ^ 2)) ≤ A := by
    have hmain : |c₃| * (s ^ 4 * n ^ 3) + 5 * D * (s ^ 4 * (N * n ^ 2)) + D ^ 2 * (s ^ 4 * (N * n ^ 2)) ≤
        (|c₃| + 5 * D + D ^ 2) * s ^ 4 * (N * n ^ 2 + n ^ 3) := by
      have h1 : 0 ≤ 5 * D * (s ^ 4 * n ^ 3) := by positivity
      have h2 : 0 ≤ D ^ 2 * (s ^ 4 * n ^ 3) := by positivity
      have h3 : 0 ≤ |c₃| * (s ^ 4 * (N * n ^ 2)) := by positivity
      linarith
    linarith
  have h5 : 5 * s * o ≤ 5 * D * (s ^ 4 * (N * n ^ 2)) := by
    have : s * o ≤ s * (D * N * n) := mul_le_mul_of_nonneg_left ho' hs0
    have : D * (s * N * n) ≤ D * (s ^ 4 * (N * n ^ 2)) := mul_le_mul_of_nonneg_left hsn hD0
    linarith
  have h6 : D * D * s * N * n ≤ D ^ 2 * (s ^ 4 * (N * n ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hsn (mul_nonneg hD0 hD0)
    linarith
  linarith

end

end Formalism.FourierDecayAlt.P.CutBP.PolTop

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `Cb`. Take `⟨c₃, hc₃⟩` from `PolTop.vector_valued_orbital_linear`. Use `⟨|c₃| + 5 * max Cb 0 + max Cb 0 ^ 2, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε c`. Take `⟨hχ, hCb, hf, hfA, hth, -⟩` from `hH`.

Establish `hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq)` using `fun g₀ _ => ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩`. Use `set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'`. Establish `hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F'` using `ckOn_fpm p p₀ hf hid`. Establish `hF'A` using `inCC_fpm_id p p₀ hfA`. Use `set u := D.cutF p.T.base χ' F' ε with hu`.

Use `set v := D.cutF p.T.base χ F' ε with hv`. Use `set m := D.cutF p.T.base (midCut χ' χ) F' ε with hm`. Establish `hm_eq : m = fun x => (1 / 2 : ℂ) • u x + (1 / 2 : ℂ) • v x`. Use function extensionality and compare the values at `x`. Simplify using `only [hm, hu, hv, D.cutF, midCut, smul_smul, ← add_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hu_ck` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ' hF'ck ε`. Establish `hv_ck` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF'ck ε`.

Take `⟨δ', hδ', hz'⟩` from `hχ'.2.1`. Take `⟨δ, hδ, hz⟩` from `hχ.2.1`. Use `set ε₀ : ℝ := min δ' δ * ε with hε₀def`. Establish `hε₀ : 0 < ε₀` using `mul_pos (lt_min hδ' hδ) hε`. Establish `hu0 : ∀ x, Gf P.k P.r p.T.base.z p.T.base.z' x < ε₀ → u x = 0`.

Introduce `x hx`. Establish `h1 : Gf P.k P.r p.T.base.z p.T.base.z' x / ε < δ'`. Rewrite using `[div_lt_iff₀ hε]`. Conclude with `lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right (min_le_left _ _) hε.le)`. Simplify using `only [hu, D.cutF, hz' _ h1, Complex.ofReal_zero, zero_smul]`.

Establish `hv0 : ∀ x, Gf P.k P.r p.T.base.z p.T.base.z' x < ε₀ → v x = 0`. Introduce `x hx`. Establish `h1 : Gf P.k P.r p.T.base.z p.T.base.z' x / ε < δ`. Rewrite using `[div_lt_iff₀ hε]`. Conclude with `lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right (min_le_right _ _) hε.le)`.

Simplify using `only [hv, D.cutF, hz _ h1, Complex.ofReal_zero, zero_smul]`. Establish `key : ∀ e : Wd.Ix (Fin w.length), ∀ q : C.LPt, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e m) q = (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e u) q + (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e v) q`. Introduce `e q`. Take `⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩` from `hCb w hw.1 e`. Establish `hdom : ∀ g ∈ B.GPos p.T.base, g ∈ C6.domL p.T.base ∅` using `fun g hg => ⟨hg.1, hg.2, fun l hl => absurd hl (Finset.notMem_empty l)⟩`.

Use `set A₁ : ℝ := A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - 2 * ((P.r : ℝ) + 1) * o with hA₁def`. Establish `hA₁ : A₁ + 2 * ((P.r : ℝ) + 1) * (o : ℝ) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)` using `le_of_eq (by rw [hA₁def]; ring)`. Take `⟨bu, hbu⟩` from `Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ' hF'A hε A₁ o hA₁`. Take `⟨bv, hbv⟩` from `Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hF'A hε A₁ o hA₁`. Take `⟨K, hK0, hKd⟩` from `PolTop.op_cut_dec p.T.base fib hfib hIn hε₀`.

Take `⟨cu, du⟩` from `hKd u A₁ bu hbu hu_ck hu0`. Take `⟨cv, dv⟩` from `hKd v A₁ bv hbv hv_ck hv0`. Use `set Ae : ℝ := A₁ - ((κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o) with hAedef`. Establish `hbu0` using `Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbu`. Establish `hbv0` using `Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbv`.

Establish `hthr : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ Ae`. Use `PolTop.weight_threshold_budget_inequality c₃ Cb (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) P.r P.k N w.length o κ hN ho hκ hth` as an intermediate fact. Rewrite using `[hAedef, hA₁def]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKK : 0 ≤ K * bu + K * bv` using `add_nonneg (mul_nonneg hK0 hbu0) (mul_nonneg hK0 hbv0)`.

Establish `bdu : ∀ g ∈ B.GPos p.T.base, ‖B.opApply Dop u g‖ ≤ (K * bu + K * bv) * B.gN g ^ (-Ae)` using `fun g hg => (du g hg).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hK0 hbv0)) (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg g) _))`. Establish `bdv : ∀ g ∈ B.GPos p.T.base, ‖B.opApply Dop v g‖ ≤ (K * bu + K * bv) * B.gN g ^ (-Ae)` using `fun g hg => (dv g hg).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hK0 hbu0)) (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg g) _))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hm_eq]`. Conclude with `PolTop.diff_operator_apply_linear Dop hu_ck hv_ck _ _ g hg.1)`.

Use `_ = (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop u) q + (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop v) q := hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ q Ae hthr _ _ (K * bu + K * bv) hKK cu cv bdu bdv _ _`. Use `_ = _ := by`. Rewrite using `[Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => (hΘ u g (hdom g hg)).symm), Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => (hΘ v g (hdom g hg)).symm)]`. Establish `hpair : ∀ γ : C.LPt, (topPair p m m w γ).re = (topPair p u u w γ).re / 4 + (topPair p v v w γ).re / 4 + (topPair p u v w γ).re / 2`. Introduce `γ`.

Unfold `topPair`. Distinguish the cases in `hw0 : w = []`. Simplify using `only [if_pos hw0]`. Substitute `hw0` using the available equality. Establish `k0` using `key (fun i => i.elim0) γ`.

Rewrite `k0` using `[p.Θ.nil, p.Θ.nil, p.Θ.nil]`. Unfold `KB.Pl.V`. Rewrite using `[k0]`. Conclude with `PolTop.hs_mid _ _`. Simplify using `only [if_neg hw0, Complex.re_sum, Complex.re_ofReal_mul]`.

Repeatedly rewrite using `[key, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, PolTop.hs_mid]`. Simplify using `only [mul_add, Finset.sum_add_distrib, Finset.sum_div, mul_div_assoc]`. Rewrite using `[← topPD_self p m, ← topPD_self p u, ← topPD_self p v]`. Unfold `topPD`. Distinguish the cases in `hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)`.

Simplify using `only [if_pos hl, Complex.re_ofReal_mul]`. Rewrite using `[hpair]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_neg hl, mul_zero, Complex.zero_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem top_middle_all_levels_holds : NFTopMidAll := by
  intro Cb
  obtain ⟨c₃, hc₃⟩ := PolTop.vector_valued_orbital_linear
  refine ⟨|c₃| + 5 * max Cb 0 + max Cb 0 ^ 2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε c
  obtain ⟨hχ, hCb, hf, hfA, hth, -⟩ := hH
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := ckOn_fpm p p₀ hf hid
  have hF'A := inCC_fpm_id p p₀ hfA
  set u := D.cutF p.T.base χ' F' ε with hu
  set v := D.cutF p.T.base χ F' ε with hv
  set m := D.cutF p.T.base (midCut χ' χ) F' ε with hm
  have hm_eq : m = fun x => (1 / 2 : ℂ) • u x + (1 / 2 : ℂ) • v x := by
    funext x
    simp only [hm, hu, hv, D.cutF, midCut, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hu_ck := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ' hF'ck ε
  have hv_ck := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF'ck ε
  obtain ⟨δ', hδ', hz'⟩ := hχ'.2.1
  obtain ⟨δ, hδ, hz⟩ := hχ.2.1
  set ε₀ : ℝ := min δ' δ * ε with hε₀def
  have hε₀ : 0 < ε₀ := mul_pos (lt_min hδ' hδ) hε
  have hu0 : ∀ x, Gf P.k P.r p.T.base.z p.T.base.z' x < ε₀ → u x = 0 := by
    intro x hx
    have h1 : Gf P.k P.r p.T.base.z p.T.base.z' x / ε < δ' := by
      rw [div_lt_iff₀ hε]
      exact lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right (min_le_left _ _) hε.le)
    simp only [hu, D.cutF, hz' _ h1, Complex.ofReal_zero, zero_smul]
  have hv0 : ∀ x, Gf P.k P.r p.T.base.z p.T.base.z' x < ε₀ → v x = 0 := by
    intro x hx
    have h1 : Gf P.k P.r p.T.base.z p.T.base.z' x / ε < δ := by
      rw [div_lt_iff₀ hε]
      exact lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right (min_le_right _ _) hε.le)
    simp only [hv, D.cutF, hz _ h1, Complex.ofReal_zero, zero_smul]

  have key : ∀ e : Wd.Ix (Fin w.length), ∀ q : C.LPt,
      D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e m) q =
        (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e u) q +
          (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e v) q := by
    intro e q
    obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hCb w hw.1 e
    have hdom : ∀ g ∈ B.GPos p.T.base, g ∈ C6.domL p.T.base ∅ := fun g hg =>
      ⟨hg.1, hg.2, fun l hl => absurd hl (Finset.notMem_empty l)⟩
    set A₁ : ℝ := A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - 2 * ((P.r : ℝ) + 1) * o with hA₁def
    have hA₁ : A₁ + 2 * ((P.r : ℝ) + 1) * (o : ℝ) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) :=
      le_of_eq (by rw [hA₁def]; ring)
    obtain ⟨bu, hbu⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ' hF'A hε A₁ o hA₁
    obtain ⟨bv, hbv⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hF'A hε A₁ o hA₁
    obtain ⟨K, hK0, hKd⟩ := PolTop.op_cut_dec p.T.base fib hfib hIn hε₀
    obtain ⟨cu, du⟩ := hKd u A₁ bu hbu hu_ck hu0
    obtain ⟨cv, dv⟩ := hKd v A₁ bv hbv hv_ck hv0
    set Ae : ℝ := A₁ - ((κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o) with hAedef
    have hbu0 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbu
    have hbv0 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbv
    have hthr : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ Ae := by
      have := PolTop.weight_threshold_budget_inequality c₃ Cb (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) P.r P.k N w.length o κ hN ho hκ hth
      rw [hAedef, hA₁def]
      linarith
    have hKK : 0 ≤ K * bu + K * bv := add_nonneg (mul_nonneg hK0 hbu0) (mul_nonneg hK0 hbv0)
    have bdu : ∀ g ∈ B.GPos p.T.base, ‖B.opApply Dop u g‖ ≤ (K * bu + K * bv) * B.gN g ^ (-Ae) := fun g hg =>
      (du g hg).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hK0 hbv0))
        (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg g) _))
    have bdv : ∀ g ∈ B.GPos p.T.base, ‖B.opApply Dop v g‖ ≤ (K * bu + K * bv) * B.gN g ^ (-Ae) := fun g hg =>
      (dv g hg).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hK0 hbu0))
        (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg g) _))
    calc D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e m) q = D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop m) q :=
          Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => hΘ m g (hdom g hg))
      _ = D.vecV p.T.base p.ν' p.m₀
            (fun g => (1 / 2 : ℂ) • B.opApply Dop u g + (1 / 2 : ℂ) • B.opApply Dop v g) q :=
          Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => by
            rw [hm_eq]; exact PolTop.diff_operator_apply_linear Dop hu_ck hv_ck _ _ g hg.1)
      _ = (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop u) q +
            (1 / 2 : ℂ) • D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop v) q :=
          hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ q Ae hthr _ _ (K * bu + K * bv) hKK cu cv bdu bdv _ _
      _ = _ := by
          rw [Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => (hΘ u g (hdom g hg)).symm),
            Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => (hΘ v g (hdom g hg)).symm)]

  have hpair : ∀ γ : C.LPt, (topPair p m m w γ).re =
      (topPair p u u w γ).re / 4 + (topPair p v v w γ).re / 4 + (topPair p u v w γ).re / 2 := by
    intro γ
    unfold topPair
    by_cases hw0 : w = []
    · simp only [if_pos hw0]
      subst hw0
      have k0 := key (fun i => i.elim0) γ
      rw [p.Θ.nil, p.Θ.nil, p.Θ.nil] at k0
      unfold KB.Pl.V
      rw [k0]
      exact PolTop.hs_mid _ _
    · simp only [if_neg hw0, Complex.re_sum, Complex.re_ofReal_mul]
      simp_rw [key, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, PolTop.hs_mid]
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_div, mul_div_assoc]
  rw [← topPD_self p m, ← topPD_self p u, ← topPD_self p v]
  unfold topPD
  by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
  · simp only [if_pos hl, Complex.re_ofReal_mul]
    rw [hpair]
    ring
  · simp only [if_neg hl, mul_zero, Complex.zero_re]
    ring

end

end Formalism.FourierDecayAlt.P.CutBP
