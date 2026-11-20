import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

/- English proof (translation)
Distinguish the cases in `hl : D.IsLocPt a i ∧ D.IsLocPt b i`. Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]`. Establish `hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r, D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g` using `fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)`. Establish `hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)), ∀ γ ∈ B.GV P.k (P.r - D.ptSize q), D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ …`.

Introduce `q hq e γ hγ`. Establish `h1` using `Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit) (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) (fun g hg _ => by simp [hU e g hg]) γ hγ`. Simplify using `only [Finset.sum_singleton, one_smul] at h1`. Conclude with `h1.symm`. Use `Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)` and prove the remaining obligations.

Simplify using `only [D.castF]`. Conclude with `hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)`. Simplify using `only [D.castF]`. Conclude with `hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)`. Rewrite using `[PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]`.
-/
theorem rr_congr_below {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F)
    (hE : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) (i : ℕ) (hi : i ≤ P.r) (hi1 : 1 ≤ i) (w : List C.Letter)
    (a b : C.LPt) : p.RR F i w a b = p.RR F₂ i w a b := by
  by_cases hl : D.IsLocPt a i ∧ D.IsLocPt b i
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]
    have hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r,
        D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g :=
      fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ
        (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)
    have hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)),
        ∀ γ ∈ B.GV P.k (P.r - D.ptSize q),
        D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ =
          D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) q γ := by
      intro q hq e γ hγ
      have h1 := Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit)
        (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e)
        (fun g hg _ => by simp [hU e g hg]) γ hγ
      simp only [Finset.sum_singleton, one_smul] at h1
      exact h1.symm
    refine Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)
    · simp only [D.castF]
      exact hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
    · simp only [D.castF]
      exact hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
  · rw [PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p F hF i hi w hw h h' m hm hsz hsz'`. Establish `hi1 : 1 ≤ i` using `by omega`. Establish `hF0` using `hF`. Take `⟨hs, -, ⟨δ, hδ, hG⟩⟩` from `hF`. Establish `heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g` using `cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl`.

Take `⟨Cs, -, hSQ⟩` from `Formalism.FourierDecayAlt.P.LastBlockContinuity.sliceContQ`. Establish `hk2 : 2 ≤ P.k` using `p.hl.2.2`. Use `set N : ℕ := w.length with hN`. Use `set A₀ : ℝ := Cs * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) with hA₀`. Use `set M : ℕ := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM`.

Take `⟨εn, hn⟩` from `Formalism.FourierDecayAlt.P.PBG.nice_of_cpt p.T.base hF0`. Take `⟨cF, hcF⟩` from `hn.2.1 A₀ M`. Establish `hcut : ContinuousOn (fun cc : ℂ × ℂ => p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))`. Use `Formalism.FourierDecayAlt.P.LastBlockContinuity.rrBelow_cont P p Formalism.FourierDecayAlt.P.Topx2.chi0 δ F i hi w N le_rfl h h' m hm hsz hsz' ?_ ?_` and prove the remaining obligations. Introduce `hh t0 ht0`.

Take `⟨ε', hε', H⟩` from `hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2 Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h m hsz) hh hm hsz t0 ht0`. Conclude with `⟨ε', hε', fun e => H e F cF hs hcF⟩`. Introduce `hh t0 ht0`. Take `⟨ε', hε', H⟩` from `hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2 Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h' m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h' m hsz') hh hm hsz' t0 ht0`. Conclude with `⟨ε', hε', fun e => H e F cF hs hcF⟩`.

Use `hcut.congr fun cc _ => ?_` and prove the remaining obligations. Conclude with `rr_congr_below p hF0 (fun g hg => (heq g hg).symm) i hi hi1 w _ _`.
-/
theorem rank_below_compact : RRBelowCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F hF i hi w hw h h' m hm hsz hsz'
  have hi1 : 1 ≤ i := by omega
  have hF0 := hF
  obtain ⟨hs, -, ⟨δ, hδ, hG⟩⟩ := hF
  have heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g :=
    cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl
  obtain ⟨Cs, -, hSQ⟩ := Formalism.FourierDecayAlt.P.LastBlockContinuity.sliceContQ
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set N : ℕ := w.length with hN
  set A₀ : ℝ := Cs * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)
    with hA₀
  set M : ℕ := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨εn, hn⟩ := Formalism.FourierDecayAlt.P.PBG.nice_of_cpt p.T.base hF0
  obtain ⟨cF, hcF⟩ := hn.2.1 A₀ M
  have hcut : ContinuousOn (fun cc : ℂ × ℂ => p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) i w
      (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
    refine Formalism.FourierDecayAlt.P.LastBlockContinuity.rrBelow_cont P p Formalism.FourierDecayAlt.P.Topx2.chi0 δ F i hi w N le_rfl h h' m hm hsz hsz' ?_ ?_
    · intro hh t0 ht0
      obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2
        Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h m hsz) hh hm hsz t0 ht0
      exact ⟨ε', hε', fun e => H e F cF hs hcF⟩
    · intro hh t0 ht0
      obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2
        Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h' m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h' m hsz') hh hm hsz' t0 ht0
      exact ⟨ε', hε', fun e => H e F cF hs hcF⟩
  refine hcut.congr fun cc _ => ?_
  exact rr_congr_below p hF0 (fun g hg => (heq g hg).symm) i hi hi1 w _ _

/- English proof (translation)
The claim follows from `germContAll_of rank_below_compact`.
-/
theorem germ_continuity_all_levels : GermContAll := germContAll_of rank_below_compact

end

end Formalism.FourierDecayAlt.P.CutBP
