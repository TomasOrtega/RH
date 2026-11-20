import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Dc Φ hF ρ`. Take `⟨-, -, hM, hS, -⟩` from `hF`. Establish `hT : Tz P.k P.r Bs.z = P.T` using `hpl.2.2.2.1`. Establish `hT' : Tz P.k P.r Bs.z' = P.T'` using `hpl.2.2.2.2.1`. Use `set Qs := MA.Qset P.r P.TT with hQs`.

Establish `hζ : ∀ x ∈ Qs, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2`. Introduce `x hx`. Rewrite using `[hT, hT']`. Conclude with `hx.2`. Establish `hmZ : ContDiffOn ℝ ∞ (fun x : MA.E P.r => NF.muZ P.k P.r Bs.μsec x.2) Qs` using `(Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).comp contDiff_snd.contDiffOn fun x hx => hζ x hx`.

Establish `hm : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) Qs` using `contDiffOn_fst.prodMk hmZ`. Establish `hGl : ∀ x ∈ Qs, NF.muZ P.k P.r Bs.μsec x.2 ∈ Q.Glev P.k P.r (Fin.last P.r)` using `fun x hx => Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec (hζ x hx))`. Establish `hU0 : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈ {y : (Fin P.r → ℂ) × Q.Mx P.k P.r | y.1 ∈ OmX P.r ∧ y.2 ∈ Dc y.1}` using `fun x hx => ⟨hx.1, hM ⟨x, hx⟩⟩`. Establish `hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r => Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs`. Use `contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_` and prove the remaining obligations.

Take `⟨U, F, hU, hx₀U, hF, hΦF⟩` from `hS _ (hU0 x₀ hx₀) (hGl x₀ hx₀)`. Use `⟨Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U, hm.continuousOn.isOpen_inter_preimage (MA.Qset_open P.r P.TT) hU, ⟨hx₀, hx₀U⟩, ?_⟩` and prove the remaining obligations. Establish `hc : ContDiffOn ℝ ∞ (fun x : MA.E P.r => F (x.1, NF.muZ P.k P.r Bs.μsec x.2)) (Qs ∩ (Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U))` using `hF.comp (hm.mono fun x hx => hx.1) fun x hx => hx.2.2`. Conclude with `hc.congr fun x hx => hΦF _ hx.2.2 (hGl x hx.1)`. Establish `he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) Qs` using `(he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2`.

Establish `hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => ((wR P.k P.TT x.2 : ℝ) : ℂ)) Qs`. Use `Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_` and prove the remaining obligations. Unfold `wR`. Use `(((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt fun x hx => ?_` and prove the remaining obligations. Establish `h2 : P.TT < Complex.normSq x.2` using `hx.2`.

Conclude with `(pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'`. Establish `hin : ContDiffOn ℝ ∞ (fun x : MA.E P.r => inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs` using `(Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)`. Establish `hall` using `hw.mul hin`. Use `show ContDiffOn ℝ MA.sm (MA.ext _) Qs`. Use `hall.congr fun x hx => ?_` and prove the remaining obligations.

Conclude with `dif_pos hx`.
-/
theorem raw_gauge_smoothness_holds : GRawSmooth := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Dc Φ hF ρ
  obtain ⟨-, -, hM, hS, -⟩ := hF
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  set Qs := MA.Qset P.r P.TT with hQs
  have hζ : ∀ x ∈ Qs, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2 := by
    intro x hx
    rw [hT, hT']
    exact hx.2
  have hmZ : ContDiffOn ℝ ∞ (fun x : MA.E P.r => NF.muZ P.k P.r Bs.μsec x.2) Qs :=
    (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).comp contDiff_snd.contDiffOn fun x hx => hζ x hx
  have hm : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) Qs :=
    contDiffOn_fst.prodMk hmZ
  have hGl : ∀ x ∈ Qs, NF.muZ P.k P.r Bs.μsec x.2 ∈ Q.Glev P.k P.r (Fin.last P.r) := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec (hζ x hx))
  have hU0 : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈
      {y : (Fin P.r → ℂ) × Q.Mx P.k P.r | y.1 ∈ OmX P.r ∧ y.2 ∈ Dc y.1} :=
    fun x hx => ⟨hx.1, hM ⟨x, hx⟩⟩
  have hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r => Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs := by
    refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hS _ (hU0 x₀ hx₀) (hGl x₀ hx₀)
    refine ⟨Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U,
      hm.continuousOn.isOpen_inter_preimage (MA.Qset_open P.r P.TT) hU, ⟨hx₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E P.r => F (x.1, NF.muZ P.k P.r Bs.μsec x.2))
        (Qs ∩ (Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U)) :=
      hF.comp (hm.mono fun x hx => hx.1) fun x hx => hx.2.2
    exact hc.congr fun x hx => hΦF _ hx.2.2 (hGl x hx.1)
  have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) Qs :=
    (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
  have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => ((wR P.k P.TT x.2 : ℝ) : ℂ)) Qs := by
    refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
    unfold wR
    refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
      fun x hx => ?_
    have h2 : P.TT < Complex.normSq x.2 := hx.2
    exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
  have hin : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs :=
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)
  have hall := hw.mul hin
  show ContDiffOn ℝ MA.sm (MA.ext _) Qs
  refine hall.congr fun x hx => ?_
  exact dif_pos hx

end Formalism.FourierDecayAlt.P.CutMP.Gauge
