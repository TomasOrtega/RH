import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.WeilTup

variable {D : D7}

/- English proof (translation)
Assemble the required witnesses or components as `⟨by show Continuous (fun x => χ x * χ' x); exact h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩`.
-/
theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨by show Continuous (fun x => χ x * χ' x); exact h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [show ⇑χ⁻¹ = fun x => (χ x)⁻¹ from funext fun x => MonoidHom.inv_apply χ x]; exact h.1.inv, fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩`.
-/
theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨by rw [show ⇑χ⁻¹ = fun x => (χ x)⁻¹ from funext fun x => MonoidHom.inv_apply χ x]; exact h.1.inv,
    fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

/- English proof (translation)
Use `⟨hA.1, fun e he a => ?_⟩` and prove the remaining obligations. Establish `h1` using `hA.2 e he a`. Establish `h2` using `hB.2 e he a`. Rewrite `h2` using `[MonoidHom.mul_apply, MonoidHom.inv_apply, h1, pow_succ]`. Rewrite using `[pow_one]`.

Conclude with `(mul_left_cancel (mul_inv_eq_iff_eq_mul.1 h2)).symm`.
-/
theorem resEta_of_diff {μ χ : (AE D)ˣ →* Circle} {n : ℕ} (hA : ResEta D μ (n + 1)) (hB : ResEta D (μ * χ⁻¹) n) :
    ResEta D χ 1 := by
  refine ⟨hA.1, fun e he a => ?_⟩
  have h1 := hA.2 e he a
  have h2 := hB.2 e he a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, pow_succ] at h2
  rw [pow_one]
  exact (mul_left_cancel (mul_inv_eq_iff_eq_mul.1 h2)).symm

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hτ t`. Establish `hmE : ¬ Odd D.R.m`. Take `⟨a, ha⟩` from `D.R.m_even`. Introduce and unpack `⟨b, hb⟩`. Use linear arithmetic over natural numbers and integers.

Establish `hE` using `GlobalTheory.WeilDatumExistence.weilDatumExists D`. Establish `hX` using `hP.bot.hyp.2.2.2.1.chain.ωX t`. Simplify using `only [Formalism.IndefR.Lift.chrStep, if_neg hmE] at hX`. Establish `hη : ∀ j' (h' : j' + 2 * 0 + 2 = D.R.m), IsHeckeChar D (pk W).eta ∧ ResEta D (pk W).eta 1`. Introduce `j' h'`.

Establish `e : j' + 1 + 1 = D.R.m` using `by omega`. Establish `hk` using `hC.kom t (j' + 1) (by omega)`. Establish `hμH : IsHeckeChar D ((pk W).toLevCh.mu t D.R.m)`. Establish `h1 : IsHeckeChar D ((pk W).toLevCh.mu t (j' + 1 + 1))` using `hk.hecS`. Rewrite `h1` using `[e]`.

Conclude with `h1`. Establish `hμR : ResEta D ((pk W).toLevCh.mu t D.R.m) (D.sp.X'.rank + 1)`. Establish `h1 : ResEta D ((pk W).toLevCh.mu t (j' + 1 + 1)) (D.sp.X (j' + 1 + 1)).rank` using `hk.resT`. Establish `h2 : D.sp.X'.rank + f.c.Lz.rank = (D.sp.X (j' + 1 + 1)).rank` using `(f.c.oT (j' + 1 + 1) e).rank_add`. Rewrite `h1` using `[← h2, (hτ j' h').1, e]`.

Conclude with `h1`. Establish `hH : IsHeckeChar D (pk W).eta`. Establish `h1` using `hecke_mul (hecke_inv hX.hecT) hμH`. Rewrite `h1` using `[_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]`. Then use the resulting hypothesis. Conclude with `⟨hH, resEta_of_diff hμR hX.resT⟩`.

Use `⟨?_, ?_, hτ⟩` and prove the remaining obligations. Introduce `j σ h`. Take `⟨hHη, hRη⟩` from `hη (j + 2 * σ + 2) (by omega)`. Establish `hzH` using `hecke_inv hHη`. Establish `hzR` using `Formalism.L2.Theta.resEta_inv hRη`.

Establish `hk0` using `hC.kom t j (by omega)`. Establish `hk1` using `hC.kom t (j + 1) (by omega)`. Take `⟨-, -, bV, bW⟩` from `(hR.row t).sBF j (σ + 1) h`. Take `⟨-, -, fV, fW⟩` from `(hR.row t).sFB j σ h`. Establish `hL` using `(f.c.bes j (σ + 1) h).line.1`.

Establish `hL'` using `(f.c.bes (j + 1 + 1) σ (idx_step h)).line.1`. Take `⟨omz, homz⟩` from `hE (f.c.bes j (σ + 1) h).L (D.sp.X (j + 1)) (pk W).ψ (pk W).eta⁻¹ ((pk W).toLevCh.mu t (j + 1)) hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT`. Take `⟨omz', homz'⟩` from `hE (D.sp.X (j + 1)) (f.c.bes (j + 1 + 1) σ (idx_step h)).L (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1)) (pk W).eta⁻¹ hk1.std hk1.hecS hzH hk1.resS (by rw [hL']; exact hzR)`. Use `⟨(pk W).toLevCh.mu t (j + 1), (pk W).toLevCh.mu t (j + 1 + 1), (pk W).eta⁻¹, omz, omz', bV, fW, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[bW]`.

Conclude with `hk0`. Rewrite using `[bW]`. Conclude with `homz`. Rewrite using `[fV]`. Conclude with `hk1`.

Rewrite using `[fV]`. Conclude with `homz'`. Introduce `j h`. Establish `e : j + 1 + 1 = D.R.m` using `by omega`. Take `⟨hHη, hRη⟩` from `hη j h`.

Establish `hzH` using `hecke_inv hHη`. Establish `hzR` using `Formalism.L2.Theta.resEta_inv hRη`. Establish `hk0` using `hC.kom t j (by omega)`. Establish `hk1` using `hC.kom t (j + 1) (by omega)`. Take `⟨-, -, bV, bW⟩` from `(hR.row t).sBF j 0 h`.

Establish `hL` using `(f.c.bes j 0 h).line.1`. Establish `hXH : IsHeckeChar D ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹)` using `by rw [e]; exact hX.hecT`. Establish `hXR : ResEta D ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) D.sp.X'.rank` using `by rw [e]; exact hX.resT`. Take `⟨omz, homz⟩` from `hE (f.c.bes j 0 h).L (D.sp.X (j + 1)) (pk W).ψ (pk W).eta⁻¹ ((pk W).toLevCh.mu t (j + 1)) hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT`. Take `⟨omT', homT⟩` from `hE (D.sp.X (j + 1)) D.sp.X' (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1)) ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) hk1.std hk1.hecS hXH hk1.resS hXR`.

Take `⟨omz'', homz''⟩` from `hE (D.sp.X (j + 1)) f.c.Lz (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1)) (pk W).eta⁻¹⁻¹ hk1.std hk1.hecS (by rw [inv_inv]; exact hHη) hk1.resS (by rw [(hτ j h).1, inv_inv]; exact hRη)`. Establish `hμ1 : (pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹ * (pk W).eta⁻¹⁻¹ = (pk W).toLevCh.mu t (j + 1 + 1)`. Rewrite using `[inv_inv, inv_mul_cancel_right]`. Establish `key : ∀ n (e' : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X' ((pk W).toLevCh.mu t (j + 1 + 1)) ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) (Eq.rec (motive` using `fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX t) e') := by`. Introduce `n e'`.

Substitute `e'` using the available equality. Rewrite using `[e]`. Conclude with `hX`. Use `⟨(pk W).toLevCh.mu t (j + 1), (pk W).eta⁻¹, (pk W).toLevCh.mu t (j + 1 + 1), (pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹, omz, omT', omz'', bV, ?_, ?_, ?_, homT, key (j + 1) (idx_top h), homz''⟩` and prove the remaining obligations. Rewrite using `[bW]`.

Conclude with `hk0`. Rewrite using `[bW]`. Conclude with `homz`. Rewrite using `[hμ1]`. Conclude with `hk1`.
-/
theorem weilOK_fam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hτ t
  have hmE : ¬ Odd D.R.m := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hX := hP.bot.hyp.2.2.2.1.chain.ωX t
  simp only [Formalism.IndefR.Lift.chrStep, if_neg hmE] at hX
  have hη : ∀ j' (h' : j' + 2 * 0 + 2 = D.R.m), IsHeckeChar D (pk W).eta ∧ ResEta D (pk W).eta 1 := by
    intro j' h'
    have e : j' + 1 + 1 = D.R.m := by omega
    have hk := hC.kom t (j' + 1) (by omega)
    have hμH : IsHeckeChar D ((pk W).toLevCh.mu t D.R.m) := by
      have h1 : IsHeckeChar D ((pk W).toLevCh.mu t (j' + 1 + 1)) := hk.hecS
      rw [e] at h1; exact h1
    have hμR : ResEta D ((pk W).toLevCh.mu t D.R.m) (D.sp.X'.rank + 1) := by
      have h1 : ResEta D ((pk W).toLevCh.mu t (j' + 1 + 1)) (D.sp.X (j' + 1 + 1)).rank := hk.resT
      have h2 : D.sp.X'.rank + f.c.Lz.rank = (D.sp.X (j' + 1 + 1)).rank := (f.c.oT (j' + 1 + 1) e).rank_add
      rw [← h2, (hτ j' h').1, e] at h1
      exact h1
    have hH : IsHeckeChar D (pk W).eta := by
      have h1 := hecke_mul (hecke_inv hX.hecT) hμH
      rwa [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    exact ⟨hH, resEta_of_diff hμR hX.resT⟩
  refine ⟨?_, ?_, hτ⟩
  · intro j σ h
    obtain ⟨hHη, hRη⟩ := hη (j + 2 * σ + 2) (by omega)
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j (σ + 1) h
    obtain ⟨-, -, fV, fW⟩ := (hR.row t).sFB j σ h
    have hL := (f.c.bes j (σ + 1) h).line.1
    have hL' := (f.c.bes (j + 1 + 1) σ (idx_step h)).line.1
    obtain ⟨omz, homz⟩ := hE (f.c.bes j (σ + 1) h).L (D.sp.X (j + 1)) (pk W).ψ (pk W).eta⁻¹ ((pk W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omz', homz'⟩ := hE (D.sp.X (j + 1)) (f.c.bes (j + 1 + 1) σ (idx_step h)).L (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1))
      (pk W).eta⁻¹ hk1.std hk1.hecS hzH hk1.resS (by rw [hL']; exact hzR)
    refine ⟨(pk W).toLevCh.mu t (j + 1), (pk W).toLevCh.mu t (j + 1 + 1), (pk W).eta⁻¹, omz, omz', bV, fW, ?_, ?_, ?_, ?_⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [fV]; exact hk1
    · rw [fV]; exact homz'
  · intro j h
    have e : j + 1 + 1 = D.R.m := by omega
    obtain ⟨hHη, hRη⟩ := hη j h
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j 0 h
    have hL := (f.c.bes j 0 h).line.1
    have hXH : IsHeckeChar D ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) := by rw [e]; exact hX.hecT
    have hXR : ResEta D ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) D.sp.X'.rank := by rw [e]; exact hX.resT
    obtain ⟨omz, homz⟩ := hE (f.c.bes j 0 h).L (D.sp.X (j + 1)) (pk W).ψ (pk W).eta⁻¹ ((pk W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omT', homT⟩ := hE (D.sp.X (j + 1)) D.sp.X' (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1))
      ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) hk1.std hk1.hecS hXH hk1.resS hXR
    obtain ⟨omz'', homz''⟩ := hE (D.sp.X (j + 1)) f.c.Lz (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1)) (pk W).eta⁻¹⁻¹
      hk1.std hk1.hecS (by rw [inv_inv]; exact hHη) hk1.resS (by rw [(hτ j h).1, inv_inv]; exact hRη)
    have hμ1 : (pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹ * (pk W).eta⁻¹⁻¹ = (pk W).toLevCh.mu t (j + 1 + 1) := by
      rw [inv_inv, inv_mul_cancel_right]
    have key : ∀ n (e' : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X' ((pk W).toLevCh.mu t (j + 1 + 1))
        ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹)
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX t) e') := by
      intro n e'
      subst e'
      rw [e]
      exact hX
    refine ⟨(pk W).toLevCh.mu t (j + 1), (pk W).eta⁻¹, (pk W).toLevCh.mu t (j + 1 + 1),
      (pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹, omz, omT', omz'', bV, ?_, ?_, ?_, homT, key (j + 1) (idx_top h), homz''⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [hμ1]; exact hk1

end GlobalTheory.Fam.WeilTup

end
