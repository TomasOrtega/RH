import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramesOfRightTranslatePointPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNormStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.MatFrames

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie j hj hjm β x x₁ κ hx p p₁ hp hp₁`. Establish `hok` using `t.idx_ok μ`. Take `⟨hLe, -, hChi⟩` from `hTie.levMid j hj hjm β`. Establish `hLoc : ∀ P : SB t μ, ∃ g z, A.midRel j hj β P g z ∧ InFrame t.seam (A.fb j hj.le β) (t.cst μ).D P κ.1 g`. Introduce `P`.

Establish `hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1)`. Unfold `IsOver`. Rewrite using `[HeightOneSpectrum.under_asIdeal]`. Establish `hU` using `(((St j hj.le).K β).lev.U_eq κ.1).1 κ.2`. Conclude with `hLe P _ hv κ.1 hU.1 (hU.2 _)`.

Use `choose g z hgz using hLoc`. Establish `hpr : ∀ P, g P ∈ prCat (Pr` using `t.Pr) (t.cst μ).sharp j P.1 ((t.idx μ).h j (A.ib j hj β) P) := fun P => (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) j P _ (g P)).1 ⟨z P, (hgz P).1⟩`. Set `gg : ∀ P : SB t μ, GLint t.X.E (D.R.N j) P.1` to `fun P => ⟨g P, hok.int j _ P (hpr P)⟩`. Establish `hB` using `fun P => GlobalTheory.T.frames_of_right_translate_point_principal_congruence A a j hj.le β x x₁ κ.1 hx p p₁ hp hp₁ P (gg P) (hgz P).2`. Use `choose C hCp hCc hCf using hB`.

Establish `hD : ∀ P : SB t μ, 1 ≤ (t.cst μ).D P` using `fun P => hok.cst_ok.D_pos P`. Establish `hc : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (gg P * C P)⁻¹ c ∧ (c : t.X.K) = (z P)⁻¹`. Introduce `P`. Take `⟨r, hr, hrx, hz⟩` from `(hgz P).1`. Distinguish the cases in `hP : P.1 ∈ t.Pr.vGs`.

Establish `hH : redGL _ P.1 (gg P) ∈ ((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).H` using `(hok.grpG j _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun y hy => redV_redGL (gg P) hy⟩`. Establish `hlam` using `hok.chrG j _ ⟨P.1, hP⟩ ⟨_, hH⟩ (g P) r hr hrx (fun y hy => redV_redGL (gg P) hy)`. Establish `hred : redGL _ P.1 (gg P * C P)⁻¹ = (redGL _ P.1 (gg P))⁻¹`. Rewrite using `[map_inv, map_mul, GlobalTheory.TopStep.redGL_of_prinCong (hD P) (hCp P), mul_one]`. Use `⟨(((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).lam ⟨_, hH⟩)⁻¹, ⟨fun hP' => ⟨hred ▸ inv_mem hH, ?_⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv]`. Use `congr 1`. Conclude with `Subtype.ext hred.symm`. Rewrite using `[Units.val_inv_eq_inv_val, hlam, hz]`. Establish `hQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K)` using `(Finset.mem_union.mp P.2).resolve_left hP`.

Take `⟨r', hr', hr'x, hr'1⟩` from `GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime hPin.fields.ok t.pr_ok hok (j := j) hjm (A.ib j hj β) P hP (C P) (hCp P)`. Establish `hgH : gg P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H`. Rewrite using `[hok.grpQ]`. Conclude with `Subgroup.mem_subgroupOf.2 (hpr P)`. Establish `hCH : C P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H`.

Rewrite using `[hok.grpQ]`. Conclude with `Subgroup.mem_subgroupOf.2 ⟨r', hr', hr'x⟩`. Establish `hlg` using `hok.chrQ j _ ⟨P.1, hQ⟩ ⟨gg P, hgH⟩ r hr hrx`. Establish `hlC` using `hok.chrQ j _ ⟨P.1, hQ⟩ ⟨C P, hCH⟩ r' hr' hr'x`. Establish `hC1 : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨C P, hCH⟩ = 1` using `Units.ext (hlC.trans hr'1)`.

Use `⟨(((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨gg P, hgH⟩)⁻¹, ⟨fun hP' => absurd hP' hP, fun hQ' _ => ⟨inv_mem (mul_mem hgH hCH), ?_⟩⟩, ?_⟩` and prove the remaining obligations. Establish `e : (⟨(gg P * C P)⁻¹, inv_mem (mul_mem hgH hCH)⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) = ((⟨gg P, hgH⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) * ⟨C P, hCH⟩)⁻¹` using `Subtype.ext (by simp)`. Rewrite using `[e, map_inv, map_mul, hC1, mul_one]`. Rewrite using `[Units.val_inv_eq_inv_val, hlg, hz]`. Use `choose c hcL hcz using hc`.

Use `⟨fun P => (gg P * C P)⁻¹, c, fun P => ?_, hcL, ?_, fun P => ?_⟩` and prove the remaining obligations. Rewrite using `[inv_inv]`. Conclude with `hCf P`. Establish `h1` using `hChi κ g z hgz`. Establish `h2 : (((∏ P, c P : t.X.Kˣ)) : t.X.K) = (∏ P, z P)⁻¹`.

Rewrite using `[Units.coe_prod, ← Finset.prod_inv_distrib]`. Conclude with `Finset.prod_congr rfl fun P _ => hcz P`. Rewrite using `[h2, map_inv₀]`. Conclude with `eq_inv_of_mul_eq_one_left h1`. Rewrite using `[inv_inv]`.

Conclude with `GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm t.seam (A.fb j hj.le β) (t.cst μ).D P (hD P) κ.1 (g P) (C P).1 (hgz P).2 (hCc P)`.
-/
theorem frames_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie j hj hjm β x x₁ κ hx p p₁ hp hp₁
  classical
  have hok := t.idx_ok μ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid j hj hjm β
  have hLoc : ∀ P : SB t μ, ∃ g z, A.midRel j hj β P g z ∧ InFrame t.seam (A.fb j hj.le β) (t.cst μ).D P κ.1 g := by
    intro P
    have hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    have hU := (((St j hj.le).K β).lev.U_eq κ.1).1 κ.2
    exact hLe P _ hv κ.1 hU.1 (hU.2 _)
  choose g z hgz using hLoc
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp j P.1 ((t.idx μ).h j (A.ib j hj β) P) := fun P =>
    (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) j P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let gg : ∀ P : SB t μ, GLint t.X.E (D.R.N j) P.1 := fun P => ⟨g P, hok.int j _ P (hpr P)⟩
  have hB := fun P => GlobalTheory.T.frames_of_right_translate_point_principal_congruence A a j hj.le β x x₁ κ.1 hx p p₁ hp hp₁ P (gg P) (hgz P).2
  choose C hCp hCc hCf using hB
  have hD : ∀ P : SB t μ, 1 ≤ (t.cst μ).D P := fun P => hok.cst_ok.D_pos P
  have hc : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P
      (gg P * C P)⁻¹ c ∧ (c : t.X.K) = (z P)⁻¹ := by
    intro P
    obtain ⟨r, hr, hrx, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hH : redGL _ P.1 (gg P) ∈ ((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).H :=
        (hok.grpG j _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun y hy => redV_redGL (gg P) hy⟩
      have hlam := hok.chrG j _ ⟨P.1, hP⟩ ⟨_, hH⟩ (g P) r hr hrx (fun y hy => redV_redGL (gg P) hy)
      have hred : redGL _ P.1 (gg P * C P)⁻¹ = (redGL _ P.1 (gg P))⁻¹ := by
        rw [map_inv, map_mul, GlobalTheory.TopStep.redGL_of_prinCong (hD P) (hCp P), mul_one]
      refine ⟨(((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).lam ⟨_, hH⟩)⁻¹, ⟨fun hP' => ⟨hred ▸ inv_mem hH, ?_⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      · rw [← map_inv]
        congr 1
        exact Subtype.ext hred.symm
      · rw [Units.val_inv_eq_inv_val, hlam, hz]
    · have hQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      obtain ⟨r', hr', hr'x, hr'1⟩ := GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime hPin.fields.ok t.pr_ok hok (j := j) hjm (A.ib j hj β) P hP (C P) (hCp P)
      have hgH : gg P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hCH : C P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 ⟨r', hr', hr'x⟩
      have hlg := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨gg P, hgH⟩ r hr hrx
      have hlC := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨C P, hCH⟩ r' hr' hr'x
      have hC1 : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨C P, hCH⟩ = 1 := Units.ext (hlC.trans hr'1)
      refine ⟨(((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨gg P, hgH⟩)⁻¹,
        ⟨fun hP' => absurd hP' hP, fun hQ' _ => ⟨inv_mem (mul_mem hgH hCH), ?_⟩⟩, ?_⟩
      · have e : (⟨(gg P * C P)⁻¹, inv_mem (mul_mem hgH hCH)⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) =
            ((⟨gg P, hgH⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) * ⟨C P, hCH⟩)⁻¹ := Subtype.ext (by simp)
        rw [e, map_inv, map_mul, hC1, mul_one]
      · rw [Units.val_inv_eq_inv_val, hlg, hz]
  choose c hcL hcz using hc
  refine ⟨fun P => (gg P * C P)⁻¹, c, fun P => ?_, hcL, ?_, fun P => ?_⟩
  · rw [inv_inv]
    exact hCf P
  · have h1 := hChi κ g z hgz
    have h2 : (((∏ P, c P : t.X.Kˣ)) : t.X.K) = (∏ P, z P)⁻¹ := by
      rw [Units.coe_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun P _ => hcz P
    rw [h2, map_inv₀]
    exact eq_inv_of_mul_eq_one_left h1
  · rw [inv_inv]
    exact GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm t.seam (A.fb j hj.le β) (t.cst μ).D P (hD P) κ.1 (g P) (C P).1 (hgz P).2 (hCc P)

end GlobalTheory.MatFrames

end
