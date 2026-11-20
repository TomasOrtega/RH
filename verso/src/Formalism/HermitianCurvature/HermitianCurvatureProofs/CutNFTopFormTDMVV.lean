import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section orb

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem vv_choose_congr {α : Sort*} {P Q : α → Prop} (e : P = Q) (hP : ∃ x, P x) (hQ : ∃ x, Q x) :
    hP.choose = hQ.choose := by
  subst e; rfl

/- English proof (translation)
Establish `hae : D.orbIntegrand Bs γ Y =ᵐ[Bs.μSS] D.orbIntegrand Bs γ Y'` using `by filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq`. Establish `hG : 0 < Gf k r Bs.z Bs.z' (B.sgs q γ)`. Establish `e : Gf k r Bs.z Bs.z' (B.sgs q γ) = Gf k r Bs.z Bs.z' γ`. Unfold `Gf`. Rewrite using `[Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq]`.

Rewrite using `[e]`. Conclude with `hpos`. Unfold `D.orbIntegrand B.rho`. Rewrite using `[hYY _ (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV Bs hq hγ) hG]`. Establish `hP : (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS) = (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS)`.

Use function extensionality and compare the values at `θ`. Apply `propext` to reduce the goal to its premises. Apply `and_congr_right` to reduce the goal to its premises. Introduce `_`. Conclude with `integrable_congr (hae.mono fun q hq => by simp only [hq])`.

Unfold `D.orbJ`. Distinguish the cases in `h : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS`. Establish `h2 : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS` using `hP ▸ h`. Rewrite using `[dif_pos h, dif_pos h2, vv_choose_congr hP h h2]`. Apply `integral_congr_ae` to reduce the goal to its premises.

Use `filter_upwards [hae] with q hq`. Rewrite using `[hq]`. Establish `h2 : ¬∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS` using `hP ▸ h`. Rewrite using `[dif_neg h, dif_neg h2]`.
-/
theorem orbJ_congr_gpos (Bs : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) (μR : Measure (Mt k r)) (Y Y' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hYY : ∀ g ∈ B.GV k r, 0 < Gf k r Bs.z Bs.z' g → Y g = Y' g) :
    D.orbJ Bs γ μR Y = D.orbJ Bs γ μR Y' := by
  have hae : D.orbIntegrand Bs γ Y =ᵐ[Bs.μSS] D.orbIntegrand Bs γ Y' := by
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq
    have hG : 0 < Gf k r Bs.z Bs.z' (B.sgs q γ) := by
      have e : Gf k r Bs.z Bs.z' (B.sgs q γ) = Gf k r Bs.z Bs.z' γ := by
        unfold Gf
        rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hq]
      rw [e]; exact hpos
    unfold D.orbIntegrand B.rho
    rw [hYY _ (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV Bs hq hγ) hG]
  have hP : (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS) =
      (fun θ => D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS) := by
    funext θ
    apply propext
    apply and_congr_right
    intro _
    exact integrable_congr (hae.mono fun q hq => by simp only [hq])
  unfold D.orbJ
  by_cases h : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y q) Bs.μSS
  · have h2 : ∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS := hP ▸ h
    rw [dif_pos h, dif_pos h2, vv_choose_congr hP h h2]
    apply integral_congr_ae
    filter_upwards [hae] with q hq
    rw [hq]
  · have h2 : ¬∃ θ, D.IsNormCut Bs γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Bs γ Y' q) Bs.μSS := hP ▸ h
    rw [dif_neg h, dif_neg h2]

end orb

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p Y Y' hYY a`. Unfold `KB.Pl.V D.vecV`. Distinguish the cases in `h : D.IsLocPt a (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a`. Rewrite using `[dif_pos h, dif_pos h]`. Distinguish the cases in `h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN a (P.r + 1) ∧ D.IsDFrame p.T.base p.ν' p.m₀ γ`.

Rewrite using `[dif_pos h', dif_pos h']`. Take `⟨hγ, hZ, -⟩` from `h'.choose_spec`. Establish `hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose`. Rewrite using `[← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ a _ h.1 hZ]`. Conclude with `h.2`.

Conclude with `orbJ_congr_gpos p.T.base hγ hpos _ Y Y' hYY`. Rewrite using `[dif_neg h', dif_neg h']`. Rewrite using `[dif_neg h, dif_neg h]`.
-/
theorem vector_positive_cone : VecVGPos := by
  intro Wp Wq _ _ _ _ _ _ P p Y Y' hYY a
  unfold KB.Pl.V D.vecV
  by_cases h : D.IsLocPt a (P.r + 1) ∧
      0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · rw [dif_pos h, dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN a (P.r + 1) ∧
        D.IsDFrame p.T.base p.ν' p.m₀ γ
    · rw [dif_pos h', dif_pos h']
      obtain ⟨hγ, hZ, -⟩ := h'.choose_spec
      have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ a _ h.1 hZ]; exact h.2
      exact orbJ_congr_gpos p.T.base hγ hpos _ Y Y' hYY
    · rw [dif_neg h', dif_neg h']
  · rw [dif_neg h, dif_neg h]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
