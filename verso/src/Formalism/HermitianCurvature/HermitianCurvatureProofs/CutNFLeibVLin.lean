import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

/- English proof (translation)
Use extensionality with `x`. Simplify using `[ContinuousLinearMap.sum_apply, map_sum, map_smul]`.
-/
theorem nfVLin_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {ι : Type} (s : Finset ι) (a : Wp →L[ℂ] Wp) (b : Wq →L[ℂ] Wq) (c : ι → ℂ)
    (f : ι → Wq →L[ℂ] Wp) :
    a.comp ((∑ i ∈ s, c i • f i).comp b) = ∑ i ∈ s, c i • a.comp ((f i).comp b) := by
  ext x
  simp [ContinuousLinearMap.sum_apply, map_sum, map_smul]

/- English proof (translation)
Take `⟨c₃, hc₃⟩` from `Formalism.FourierDecayAlt.P.PBE.orbJ_dom`. Use `⟨c₃, ?_⟩` and prove the remaining obligations. Introduce `k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ Q c H Hq A hA hcont hdec hH pt hpt hGPoint`. Unfold `D.vecV`. Establish `h : D.IsLocPt pt (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt` using `⟨hpt, hGPoint⟩`.

Simplify using `only [dif_pos h]`. Distinguish the cases in `h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN pt (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ`. Simplify using `only [dif_pos h']`. Establish `hγ` using `h'.choose_spec.1`. Establish `hZ` using `h'.choose_spec.2.1`.

Establish `hGq` using `Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' pt h'.choose h.1 hZ`. Establish `hpos : 0 < Gf k r Bs.z Bs.z' h'.choose` using `hGq ▸ h.2`. Establish `hGeq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt = Gf k r Bs.z Bs.z' h'.choose`. Rewrite using `[hGq]`. Take `⟨hmono, hd⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' pt (r + 1) h.1.2 h.1.1`.

Establish `hrel` using `Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs pt h'.choose h.1 hγ hZ`. Establish `horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs` using `fun p hp => ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩`. Establish `hZm` using `hZ.trans hmono`. Take `⟨θ, maj, hθ, hmaj, hdom⟩` from `hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos hA`. Establish `hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _` using `⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩`.

Establish `hR` using `Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG`. Establish `hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS → D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) G = ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS`. Introduce `G hi`. Establish `hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) θ' ∧ Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS` using `⟨θ, hθ, hi⟩`. Unfold `D.orbJ`.

Rewrite using `[dif_pos hex]`. Conclude with `Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ hex.choose_spec.2 hi`. Establish `hiq : ∀ q, Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose (Hq q) p) Bs.μSS`. Introduce `q`. Take `⟨C, hC⟩` from `hdec q (Gf k r Bs.z Bs.z' h'.choose) hpos`.

Establish `hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose (Hq q)) Bs.μSS` using `Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb (hcont q)`. Use `Integrable.mono' (hmaj.const_mul (max C 0)) (hθ.1.aestronglyMeasurable.smul hm) ?_` and prove the remaining obligations. Use `hdom (Hq q) (max C 0) (le_max_right _ _) fun p hp => ?_` and prove the remaining obligations. Establish `hs` using `horb p hp`. Use `(hC _ hs.1 (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp])).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)`. Establish `hae : (fun p => θ p • D.orbIntegrand Bs h'.choose H p) =ᵐ[Bs.μSS] fun p => ∑ q, c q (Gf k r Bs.z Bs.z' h'.choose) • (θ p • D.orbIntegrand Bs h'.choose (Hq q) p)` using `by filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp`. Establish `hs` using `horb p hp`. Simplify using `only [D.orbIntegrand, B.rho]`. Rewrite using `[hH _ hs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, nfVLin_comp_sum, Finset.smul_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm (B.xiTau Bs (1, 1) p), smul_comm (θ p)]`. Establish `hiH : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose H p) Bs.μSS` using `(integrable_finsetSum _ fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))).congr hae.symm`. Establish `hint : ∀ q ∈ (Finset.univ : Finset (Fin (Q + 1))), Integrable (fun a => c q (Gf k r Bs.z Bs.z' h'.choose) • (θ a • D.orbIntegrand Bs h'.choose (Hq q) a)) Bs.μSS` using `fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))`. Rewrite using `[hEq H hiH, integral_congr_ae hae, integral_finsetSum Finset.univ hint, hGeq]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[integral_smul, hEq (Hq q) (hiq q)]`. Simplify using `only [dif_neg h', smul_zero, Finset.sum_const_zero]`.
-/
theorem vector_linearity_holds : NFVLin := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ Q c H Hq A hA hcont hdec hH pt hpt hGPoint
  unfold D.vecV
  have h : D.IsLocPt pt (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt := ⟨hpt, hGPoint⟩
  simp only [dif_pos h]
  by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN pt (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
  · simp only [dif_pos h']
    have hγ := h'.choose_spec.1
    have hZ := h'.choose_spec.2.1
    have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' pt h'.choose h.1 hZ
    have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
    have hGeq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt = Gf k r Bs.z Bs.z' h'.choose := by
      rw [hGq]
    obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' pt (r + 1) h.1.2 h.1.1
    have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs pt h'.choose h.1 hγ hZ
    have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
      ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
    have hZm := hZ.trans hmono
    obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos hA
    have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
      ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
        fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
    have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG

    have hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp),
        Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS →
        D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) G =
          ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS := by
      intro G hi
      have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) θ' ∧
          Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
      unfold D.orbJ
      rw [dif_pos hex]
      exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
        hex.choose_spec.2 hi

    have hiq : ∀ q, Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose (Hq q) p) Bs.μSS := by
      intro q
      obtain ⟨C, hC⟩ := hdec q (Gf k r Bs.z Bs.z' h'.choose) hpos
      have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose (Hq q)) Bs.μSS :=
        Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb (hcont q)
      refine Integrable.mono' (hmaj.const_mul (max C 0)) (hθ.1.aestronglyMeasurable.smul hm) ?_
      refine hdom (Hq q) (max C 0) (le_max_right _ _) fun p hp => ?_
      have hs := horb p hp
      refine (hC _ hs.1 (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp])).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

    have hae : (fun p => θ p • D.orbIntegrand Bs h'.choose H p) =ᵐ[Bs.μSS]
        fun p => ∑ q, c q (Gf k r Bs.z Bs.z' h'.choose) • (θ p • D.orbIntegrand Bs h'.choose (Hq q) p) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have hs := horb p hp
      simp only [D.orbIntegrand, B.rho]
      rw [hH _ hs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, nfVLin_comp_sum, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm (B.xiTau Bs (1, 1) p), smul_comm (θ p)]
    have hiH : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose H p) Bs.μSS :=
      (integrable_finsetSum _ fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))).congr hae.symm
    have hint : ∀ q ∈ (Finset.univ : Finset (Fin (Q + 1))), Integrable
        (fun a => c q (Gf k r Bs.z Bs.z' h'.choose) • (θ a • D.orbIntegrand Bs h'.choose (Hq q) a)) Bs.μSS :=
      fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))
    rw [hEq H hiH, integral_congr_ae hae, integral_finsetSum Finset.univ hint, hGeq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_smul, hEq (Hq q) (hiq q)]
  · simp only [dif_neg h', smul_zero, Finset.sum_const_zero]

end

end Formalism.FourierDecayAlt.P.CutBP
