import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Introduce `hJT hJR hTay Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X Y a b`. Take `⟨N, hN⟩` from `hJT (Wq →L[ℂ] Wp) P.k P.r Bs.z Bs.z' Y a b`. Establish `hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'` using `⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩`. Distinguish the cases in `hne : ∃ ζs, ζs ∈ RadTA.Ann Bs.z Bs.z'`. Use `swap`.

Conclude with `⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q hq => absurd ⟨q.2, hq.2⟩ hne⟩`. Take `⟨ζs, hζs⟩` from `hne`. Take `⟨Pr, hPr1, hPr2⟩` from `RadTA.exists_pr (RadTA.fibS Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs)`. Establish `hfib : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs`. Introduce `ζ hζ`.

Unfold `NF.Fib`. Rewrite using `[hcs.2 ζ ζs hζ hζs]`. Establish `hG : RadTA.Gd Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr` using `⟨hB, fun x ζ hζ => by rw [hfib ζ hζ]; exact hPr1 x⟩`. Establish `hPrF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', ∀ x ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Pr x = x`. Introduce `ζ hζ x hx`.

Rewrite `hx` using `[hfib ζ hζ]`. Conclude with `hPr2 x hx`. Establish `hc0 : (fun _ => (1 : ℂ)) ∈ OmX P.r` using `fun _ => one_ne_zero`. Use `⟨N, fun j => RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j, fun j => RadTA.AA_smooth hG hc0 j, ?_⟩` and prove the remaining obligations. Introduce and unpack `Φ ⟨c, ζ0⟩ hq`.

Establish `hc : c ∈ OmX P.r` using `hq.1`. Establish `hζ0 : ζ0 ∈ RadTA.Ann Bs.z Bs.z'` using `hq.2`. Establish `hmem` using `Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Φ.2`. Use `set ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ) with hψdef`. Establish `hψs : ContDiffOn ℝ ∞ ψ (RadTA.Ann Bs.z Bs.z')` using `hmem.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc, hζ⟩`.

Establish `hψF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', Pr (ψ ζ) = ψ ζ` using `fun ζ hζ => hPrF ζ hζ _ (hmem.2.1 (c, ζ) ⟨hc, hζ⟩)`. Establish `hterm : ∀ j, ContDiff ℝ ∞ (fun ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0))`. Introduce `j`. Conclude with `((iteratedFDeriv ℝ j ψ ζ0).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)).const_smul _`. Use `set tay : ℂ → (Wq →L[ℂ] Wp) := fun ζ => ∑ j ∈ Finset.range (N + 1), ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0) with htay`.

Establish `htays : ContDiff ℝ ∞ tay` using `ContDiff.sum fun j _ => hterm j`. Establish `hR` using `RadTA.radR_PhiP (μs := Bs.μsec) (π := Bs.π) (π' := Bs.π') hG htays`. Establish `hsum : ∑ j ∈ Finset.range (N + 1), RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j ζ0 (iteratedFDeriv ℝ j ψ ζ0) = RadTA.VV Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) tay ζ0` using `(Finset.sum_congr rfl fun j _ => RadTA.AA_apply hG j ζ0 _).trans (RadTA.VV_sum hG (Finset.range (N + 1)) (fun j ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) hterm ζ0).symm`. Establish `hΦtc : ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c = ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (fun _ => 1)`. Use `RadTA.fn_eq_of_radR hB _ hc hc0 fun ζ => ?_` and prove the remaining obligations.

Rewrite using `[hR]`. Distinguish the cases in `hζ : ζ ∈ RadTA.Ann Bs.z Bs.z'`. Simplify using `only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩), Set.indicator_of_mem (show ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc0, hζ⟩)]`. Simplify using `only [RadTA.phiP, Set.indicator_of_notMem (show (c, ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2), Set.indicator_of_notMem (show ((fun _ => (1 : ℂ)), ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2)]`. Establish `hT0` using `RadTA.t_slice (μs := Bs.μsec) hB X Y a b (RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) hc hc0 hΦtc hζ0`.

Establish `hz : ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) ζ0 = 0`. Introduce `i hi`. Set `Prr : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp)` to `LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)`. Establish `hev : (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) =ᶠ[nhds ζ0] (fun ζ => Prr (ψ ζ - tay ζ))` using `by filter_upwards [(RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0] with ζ hζ`. Rewrite using `[Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, hR]`.

Simplify using `only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩)]`. Use `show ψ ζ - Pr (tay ζ) = Pr (ψ ζ - tay ζ)`. Rewrite using `[map_sub, hψF ζ hζ]`. Rewrite using `[(hev.iteratedFDeriv ℝ i).eq_of_nhds]`. Establish `hcd : ContDiffAt ℝ ∞ (fun ζ => ψ ζ - tay ζ) ζ0` using `(hψs.sub htays.contDiffOn).contDiffAt ((RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0)`.

Establish `h1` using `ContinuousLinearMap.iteratedFDeriv_comp_left Prr hcd (i := i) (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))`. Establish `h2 : iteratedFDeriv ℝ i (fun ζ => ψ ζ - tay ζ) ζ0 = 0` using `hTay (Wq →L[ℂ] Wp) ψ (RadTA.Ann Bs.z Bs.z') ζ0 N (RadTA.ann_open Bs.z Bs.z') hζ0 hψs i hi`. Rewrite using `[show (fun ζ => Prr (ψ ζ - tay ζ)) = Prr ∘ (fun ζ => ψ ζ - tay ζ) from rfl, h1, h2]`. Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.compContinuousMultilinearMap_coe]`.

Simplify using the standard rewrite rules. Establish `hZ` using `hJR Wp Wq P Bs hpl hk (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) (c, ζ0) hq N hz`. Establish `hdom` using `Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem hcs.1 hq`. Establish `hv` using `hN _ _ hdom.2.1 hZ`. Establish `ht` using `X.t_apply Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) _ hdom`.

Establish `hdiff : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((X.t Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ0) = 0`. Rewrite using `[RadTA.radR_apply _ hq]`. Conclude with `ht.trans hv`. Rewrite `hdiff` using `[map_sub, Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, sub_eq_zero]`. Rewrite using `[hdiff, hT0]`.

Conclude with `hsum.symm`.
-/
theorem radial_torus_of_jets_taylor : GTCLRadTOfCut := by
  intro hJT hJR hTay Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X Y a b
  obtain ⟨N, hN⟩ := hJT (Wq →L[ℂ] Wp) P.k P.r Bs.z Bs.z' Y a b
  have hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  by_cases hne : ∃ ζs, ζs ∈ RadTA.Ann Bs.z Bs.z'
  swap
  · exact ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q hq => absurd ⟨q.2, hq.2⟩ hne⟩
  obtain ⟨ζs, hζs⟩ := hne
  obtain ⟨Pr, hPr1, hPr2⟩ := RadTA.exists_pr (RadTA.fibS Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs)
  have hfib : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ =
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs := by
    intro ζ hζ
    unfold NF.Fib
    rw [hcs.2 ζ ζs hζ hζs]
  have hG : RadTA.Gd Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr := ⟨hB, fun x ζ hζ => by rw [hfib ζ hζ]; exact hPr1 x⟩
  have hPrF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', ∀ x ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Pr x = x := by
    intro ζ hζ x hx
    rw [hfib ζ hζ] at hx
    exact hPr2 x hx
  have hc0 : (fun _ => (1 : ℂ)) ∈ OmX P.r := fun _ => one_ne_zero
  refine ⟨N, fun j => RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j,
    fun j => RadTA.AA_smooth hG hc0 j, ?_⟩
  rintro Φ ⟨c, ζ0⟩ hq
  have hc : c ∈ OmX P.r := hq.1
  have hζ0 : ζ0 ∈ RadTA.Ann Bs.z Bs.z' := hq.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Φ.2
  set ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)
    with hψdef
  have hψs : ContDiffOn ℝ ∞ ψ (RadTA.Ann Bs.z Bs.z') :=
    hmem.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc, hζ⟩
  have hψF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', Pr (ψ ζ) = ψ ζ := fun ζ hζ => hPrF ζ hζ _ (hmem.2.1 (c, ζ) ⟨hc, hζ⟩)
  have hterm : ∀ j, ContDiff ℝ ∞
      (fun ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) := by
    intro j
    exact ((iteratedFDeriv ℝ j ψ ζ0).contDiff.comp
      (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)).const_smul _
  set tay : ℂ → (Wq →L[ℂ] Wp) := fun ζ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0) with htay
  have htays : ContDiff ℝ ∞ tay := ContDiff.sum fun j _ => hterm j
  have hR := RadTA.radR_PhiP (μs := Bs.μsec) (π := Bs.π) (π' := Bs.π') hG htays

  have hsum : ∑ j ∈ Finset.range (N + 1), RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j ζ0
        (iteratedFDeriv ℝ j ψ ζ0) = RadTA.VV Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) tay ζ0 :=
    (Finset.sum_congr rfl fun j _ => RadTA.AA_apply hG j ζ0 _).trans
      (RadTA.VV_sum hG (Finset.range (N + 1))
        (fun j ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) hterm ζ0).symm

  have hΦtc : ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c = ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay :
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (fun _ => 1) := by
    refine RadTA.fn_eq_of_radR hB _ hc hc0 fun ζ => ?_
    rw [hR]
    by_cases hζ : ζ ∈ RadTA.Ann Bs.z Bs.z'
    · simp only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩),
        Set.indicator_of_mem (show ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc0, hζ⟩)]
    · simp only [RadTA.phiP, Set.indicator_of_notMem (show (c, ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2),
        Set.indicator_of_notMem (show ((fun _ => (1 : ℂ)), ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2)]
  have hT0 := RadTA.t_slice (μs := Bs.μsec) hB X Y a b (RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) hc hc0 hΦtc hζ0

  have hz : ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) ζ0 = 0 := by
    intro i hi
    let Prr : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) := LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)
    have hev : (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) =ᶠ[nhds ζ0] (fun ζ => Prr (ψ ζ - tay ζ)) := by
      filter_upwards [(RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0] with ζ hζ
      rw [Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, hR]
      simp only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩)]
      show ψ ζ - Pr (tay ζ) = Pr (ψ ζ - tay ζ)
      rw [map_sub, hψF ζ hζ]
    rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
    have hcd : ContDiffAt ℝ ∞ (fun ζ => ψ ζ - tay ζ) ζ0 :=
      (hψs.sub htays.contDiffOn).contDiffAt ((RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0)
    have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left Prr hcd (i := i)
      (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
    have h2 : iteratedFDeriv ℝ i (fun ζ => ψ ζ - tay ζ) ζ0 = 0 :=
      hTay (Wq →L[ℂ] Wp) ψ (RadTA.Ann Bs.z Bs.z') ζ0 N (RadTA.ann_open Bs.z Bs.z') hζ0 hψs i hi
    rw [show (fun ζ => Prr (ψ ζ - tay ζ)) = Prr ∘ (fun ζ => ψ ζ - tay ζ) from rfl, h1, h2]
    ext v
    rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
    simp
  have hZ := hJR Wp Wq P Bs hpl hk (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) (c, ζ0) hq N hz
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem hcs.1 hq
  have hv := hN _ _ hdom.2.1 hZ
  have ht := X.t_apply Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) _ hdom
  have hdiff : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((X.t Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) :
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ0) = 0 := by
    rw [RadTA.radR_apply _ hq]
    exact ht.trans hv
  rw [map_sub, Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, sub_eq_zero] at hdiff
  rw [hdiff, hT0]
  exact hsum.symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
