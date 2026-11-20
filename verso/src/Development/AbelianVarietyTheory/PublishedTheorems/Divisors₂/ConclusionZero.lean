import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicStd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermThetaHeckeIsotropic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsPairResThetaInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeftInvTerm
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AllHypothesesInhabited
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelCenterEquivariant
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.Core.Rk.SW (sch)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AnisoStdModel
open GlobalTheory.StdUnn GlobalTheory.RegSch GlobalTheory.Published

variable {D : D7} {n : ℕ}

/- English proof (translation)
Take `⟨ψ, χ, om, a, θ, sS, sB, m, 𝓨, ν, f, hW, ha, -, hθ, hS, hB, hK, hm, hν, hf, hf0⟩` from `GlobalTheory.SiegelWeilMiddle.Model.all_hypotheses_inhabited D A V`. Establish `hfK` using `GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ _ V 1 χ om sS sB hW hθ hS hB _ (isCompact_Khat A a) hK f hf`. Take `⟨μ, hskew, hconj⟩` from `GlobalTheory.StdUnn.ConjElt.exists_isConj D`. Take `⟨κ, hchart⟩` from `GlobalTheory.StdUnn.chart_exists D A μ hskew`. Take `⟨p, hp⟩` from `hconj A a ha κ hchart`.

Take `⟨omS, htr⟩` from `GlobalTheory.StdUnn.exists_transport_std D ψ A V χ om hW m 𝓨 hm θ hθ κ`. Establish `hP : Pass ψ θ A V χ om m 𝓨 μ κ omS` using `⟨hW, hm, hθ, hskew, hchart, htr⟩`. Take `⟨lam, hlam, hψ, -⟩` from `GlobalTheory.StdUnn.shift_char_realPar D ψ hW.std θ hθ μ hskew`. Take `⟨hχ, hr⟩` from `GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hW.hecT hW.resT`. Establish `hSS` using `GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A V m 𝓨 hm`.

Establish `h1 : IsThetaFunO ψ (dblSp A) V (om ((p : GA D (dblSp A))⁻¹, 1) f)` using `hW.om_pres _ _ hf.1`. Set `Φ : schwartzA θ V.rank A.rank` to `⟨_, hSS.1 _ h1⟩`. Use `⟨_, _, θ, m, 𝓨, omS, _, ν, Φ, hψ, hχ, hr, hθ, hm, pass_isWeilSch D ψ θ A V χ om m 𝓨 μ κ omS hP lam hlam, isHeight_hgtStd D A μ hskew κ hchart a p hp, hν, kfin_of_conj D ψ θ A V χ om m 𝓨 μ κ omS hP a p hp f hf.1 hfK 1 Φ rfl, fun h0 => hf0 ?_, fun hV g => ?_⟩` and prove the remaining obligations. Establish `hz : IsThetaFunO ψ (dblSp A) V 0`. Simplify using `using (GlobalTheory.StdUnn.sch_linear D ψ hW.std A V m 𝓨 hm f f hf.1 hf.1 0).2.1`.

Establish `hz' : sch ψ A V m 𝓨 0 = 0`. Simplify using `using (GlobalTheory.StdUnn.sch_linear D ψ hW.std A V m 𝓨 hm f f hf.1 hf.1 0).2.2.2`. Establish `h2 : om ((p : GA D (dblSp A))⁻¹, 1) f = 0` using `hSS.2.2 _ _ h1 hz ((congrArg Subtype.val h0).trans hz'.symm)`. Establish `h3` using `congrArg (om ((p : GA D (dblSp A)), 1)) h2`. Rewrite `h3` using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one, Module.End.one_apply, map_zero]`. Then use the resulting hypothesis.

Use `haveI := hν`. Establish `e : theta omS Φ g = fun h => thetaKO om (κ.symm g) h (om ((p : GA D (dblSp A))⁻¹, 1) f)` using `funext fun h => by`. Use `FirstTermHeckeIso.theta_chart hP h1 Φ rfl (κ.symm g) 1 h` as an intermediate fact. Simplify `this` using `[Prod.mk_one_one]`. Rewrite using `[e]`.

Conclude with `GlobalTheory.ThetaMean.integrable_theta hW h1 (GlobalTheory.Mem.AnisoQuotient.exists_compact D V hV) _`.
-/
theorem data (D : D7) (A V : HSp D) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank A.rank)) (𝓕 : Set (Mx D V.rank A.rank))
    (ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank)) (H : G D A.rank → ℝ≥0) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank A.rank),
    IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ ResEta D χ V.rank ∧ IsInfFam θ ∧ IsCovolOne (ratMx D V.rank A.rank) μ 𝓕 ∧
      IsWeilSch ψ χ θ V μ ω ∧ IsHeight H ∧ ν.IsHaarMeasure ∧ KFin ω Φ ∧ Φ ≠ 0 ∧
      (IsAniso V → ∀ g, Integrable (AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν)) := by
  obtain ⟨ψ, χ, om, a, θ, sS, sB, m, 𝓨, ν, f, hW, ha, -, hθ, hS, hB, hK, hm, hν, hf, hf0⟩ :=
    GlobalTheory.SiegelWeilMiddle.Model.all_hypotheses_inhabited D A V
  have hfK := GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ _ V 1 χ om sS sB hW hθ hS hB _ (isCompact_Khat A a) hK f hf
  obtain ⟨μ, hskew, hconj⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hchart⟩ := GlobalTheory.StdUnn.chart_exists D A μ hskew
  obtain ⟨p, hp⟩ := hconj A a ha κ hchart
  obtain ⟨omS, htr⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A V χ om hW m 𝓨 hm θ hθ κ
  have hP : Pass ψ θ A V χ om m 𝓨 μ κ omS := ⟨hW, hm, hθ, hskew, hchart, htr⟩
  obtain ⟨lam, hlam, hψ, -⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ hW.std θ hθ μ hskew
  obtain ⟨hχ, hr⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hW.hecT hW.resT
  have hSS := GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A V m 𝓨 hm
  have h1 : IsThetaFunO ψ (dblSp A) V (om ((p : GA D (dblSp A))⁻¹, 1) f) := hW.om_pres _ _ hf.1
  let Φ : schwartzA θ V.rank A.rank := ⟨_, hSS.1 _ h1⟩
  refine ⟨_, _, θ, m, 𝓨, omS, _, ν, Φ, hψ, hχ, hr, hθ, hm, pass_isWeilSch D ψ θ A V χ om m 𝓨 μ κ omS hP lam hlam,
    isHeight_hgtStd D A μ hskew κ hchart a p hp, hν, kfin_of_conj D ψ θ A V χ om m 𝓨 μ κ omS hP a p hp f hf.1 hfK 1 Φ rfl,
    fun h0 => hf0 ?_, fun hV g => ?_⟩
  · have hz : IsThetaFunO ψ (dblSp A) V 0 := by
      simpa using (GlobalTheory.StdUnn.sch_linear D ψ hW.std A V m 𝓨 hm f f hf.1 hf.1 0).2.1
    have hz' : sch ψ A V m 𝓨 0 = 0 := by
      simpa using (GlobalTheory.StdUnn.sch_linear D ψ hW.std A V m 𝓨 hm f f hf.1 hf.1 0).2.2.2
    have h2 : om ((p : GA D (dblSp A))⁻¹, 1) f = 0 := hSS.2.2 _ _ h1 hz ((congrArg Subtype.val h0).trans hz'.symm)
    have h3 := congrArg (om ((p : GA D (dblSp A)), 1)) h2
    rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
      Module.End.one_apply, map_zero] at h3
  · haveI := hν
    have e : theta omS Φ g = fun h => thetaKO om (κ.symm g) h (om ((p : GA D (dblSp A))⁻¹, 1) f) := funext fun h => by
      have := FirstTermHeckeIso.theta_chart hP h1 Φ rfl (κ.symm g) 1 h
      simpa [Prod.mk_one_one] using this
    rw [e]
    exact GlobalTheory.ThetaMean.integrable_theta hW h1 (GlobalTheory.Mem.AnisoQuotient.exists_compact D V hV) _

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.OrthSumSp.posSp D n, GlobalTheory.OrthSumSp.posSp D m, rfl, rfl, GlobalTheory.RegSW.WeakModel.isAniso_pos D m⟩`.
-/
theorem ranks (D : D7) (n m : ℕ) : ∃ A V : HSp D, A.rank = n ∧ V.rank = m ∧ IsAniso V :=
  ⟨GlobalTheory.OrthSumSp.posSp D n, GlobalTheory.OrthSumSp.posSp D m, rfl, rfl, GlobalTheory.RegSW.WeakModel.isAniso_pos D m⟩

/- English proof (translation)
The claim follows from `funext fun g => by obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp rw [h p hp a ha k hk, h' p hp a ha k hk]`.
-/
theorem height_unique {H H' : G D n → ℝ≥0} (h : IsHeight H) (h' : IsHeight H') : H = H' := funext fun g => by
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
  rw [h p hp a ha k hk, h' p hp a ha k hk]

/- English proof (translation)
The claim follows from `LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hχ hω H hH Φ z`.
-/
theorem leftInv {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) {H : G D n → ℝ≥0} (hH : IsHeight H) (Φ : schwartzA θ V.rank n) (z : ℂ) :
    LeftInv (P D n ⊓ GF D n) (sect ω H Φ z) :=
  LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hχ hω H hH Φ z

/- English proof (translation)
Establish `h1 : (fun z => Eis.cosetSum (P D n) (GF D n) (sect ω H 0 z) g) = fun _ => 0`. Use function extensionality and compare the values at `z`. Simplify using `[Eis.cosetSum, Eis.term, sect]`. Establish `h2 : thetaInt ω ν 0 g = 0`. Simplify using `[thetaInt, theta, AutomorphicL2Unitary.descend]`.

Rewrite using `[h1, h2, mul_zero]`. Conclude with `holValueAt_const 0 _`.
-/
theorem conclusion_zero {V : HSp D} {θ} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (ν : Measure (GA D V)) (c : ℂ) (g : G D n) :
    HolValueAt (fun z => Eis.cosetSum (P D n) (GF D n) (sect ω H 0 z) g) (s0 V n) (c * thetaInt ω ν 0 g) := by
  have h1 : (fun z => Eis.cosetSum (P D n) (GF D n) (sect ω H 0 z) g) = fun _ => 0 := by
    funext z; simp [Eis.cosetSum, Eis.term, sect]
  have h2 : thetaInt ω ν 0 g = 0 := by
    simp [thetaInt, theta, AutomorphicL2Unitary.descend]
  rw [h1, h2, mul_zero]
  exact holValueAt_const 0 _

/- English proof (translation)
Use `h1.unique h2` as an intermediate fact. Take the linear combination `-this`.
-/
theorem const_unique {h : ℂ → ℂ} {s I : ℂ} (h1 : HolValueAt h s (1 * I)) (h2 : HolValueAt h s (2 * I)) : I = 0 := by
  have := h1.unique h2
  linear_combination -this

end GlobalTheory.AnisoStdModel

end
