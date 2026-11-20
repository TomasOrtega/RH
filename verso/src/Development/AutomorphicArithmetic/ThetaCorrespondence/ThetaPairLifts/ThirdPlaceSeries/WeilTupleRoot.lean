import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.TupRoot
variable {D : D7}
end GlobalTheory.TupRoot
open GlobalTheory.TupRoot in
/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W u f hP _hR t`. Establish `hc` using `hP.bot.hyp.2.2.2.1`. Establish `hL` using `hc.lev`. Take `⟨n, hn0, hn⟩` from `hL.xi_fin t`. Establish `hxi : ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) ((_root_.GlobalTheory.Fam.pk_z W).xiH t)` using `hL.xi t`.

Establish `hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1` using `MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))`. Establish `hstep : ∀ k, Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta k = ((Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).1 * (_root_.GlobalTheory.Fam.pk_z W).xi t, (Lift.chr …`. Introduce `k`. Unfold `Lift.chrStep`. Apply the tactic sequence `split_ifs <;> simp [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_right_comm]`.

Establish `hpow : ∀ x, (_root_.GlobalTheory.Fam.pk_z W).xi t x ^ n = 1` using `pow_eq_one_of_chrEq hxi hn`. Establish `hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (_root_.GlobalTheory.Fam.pk_z W).xi t x = 1` using `eq_one_of_finPart hxi hn0 hn`. Use `choose xr hxr using fun k => GlobalTheory.RecDict.exists_isDetRoot D (Yc D k) (f.g.b k)`. Take `⟨xT, hxT⟩` from `GlobalTheory.RecDict.exists_isDetRoot D D.sp.X' f.g.bT`. Set `w : ℕ → Circle` to `fun k => if k + 1 < D.R.m then ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (xr (k + 1)) else ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT`.

Use `⟨fun k => (w k : ℂ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Use `⟨n, hn0, ?_⟩` and prove the remaining obligations. Establish `h1 : w k ^ n = 1`. Simplify using `only [w]`.

Apply the tactic sequence `split_ifs <;> rw [mul_pow, inv_pow, hpow, hpow, inv_one, one_mul]`. Use `congrArg (fun z : Circle => (z : ℂ)) h1` as an intermediate fact. Simplify using `using this`. Introduce `j hj _ _ a ha a' ha' g hg`. Establish `hW0` using `hc.chain.ωY W.P.A3.A.μ0 j hj`.

Establish `hWt` using `hc.chain.ωY t j hj`. Rewrite `hWt` using `[hstep]`. Take `⟨z, hz⟩` from `GlobalTheory.RecDict.exists_isDetRoot D (Yc D j) a`. Take `⟨y, hy1, hy⟩` from `GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a ha z hz`. Take `⟨z', hz'⟩` from `GlobalTheory.RecDict.exists_isDetRoot D (Yc D (j + 1)) a'`.

Take `⟨y', hy1', hy'⟩` from `GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a' ha' z' hz'`. Rewrite using `[twist_eq hW0 hWt (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy (hxr j)) (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy' (hxr (j + 1))) hg]`. Establish `e : ((_root_.GlobalTheory.Fam.pk_z W).xi t (y * xr j))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (y' * xr (j + 1)) = w j`. Simplify using `only [w, if_pos hj, map_mul, hinf _ hy1, hinf _ hy1', one_mul]`. Rewrite using `[e]`.

Introduce `j h g hg`. Establish `hW0` using `isWeil_rec (idx_top h) _ (hc.chain.ωX W.P.A3.A.μ0)`. Establish `hWt` using `isWeil_rec (idx_top h) _ (hc.chain.ωX t)`. Rewrite `hWt` using `[hstep]`. Establish `e` using `twist_eq hW0 hWt (hxr (j + 1)) hxT hg`.

Establish `hw : w (j + 1) = ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr (j + 1)))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT`. Simplify using `only [w]`. Rewrite using `[if_neg (by omega)]`. Use `show _ = ((w (j + 1) : Circle) : ℂ) • _`. Rewrite using `[hw]`.

Conclude with `e`. Introduce `j`. Use `⟨n, hn0, ?_⟩` and prove the remaining obligations. Establish `hν : (_root_.GlobalTheory.Fam.pk_z W).xi t ^ n = 1` using `MonoidHom.ext fun x => by simpa using hpow x`. Simplify using `only [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_one, mul_pow, hν]`.
-/
theorem GlobalTheory.TupRoot.weil_tuple_root_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → (_root_.GlobalTheory.Fam.pk_z W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ g → omT (_root_.GlobalTheory.Fam.pk_z W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t j ^ n = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP _hR t
  have hc := hP.bot.hyp.2.2.2.1
  have hL := hc.lev
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have hxi : ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) ((_root_.GlobalTheory.Fam.pk_z W).xiH t) := hL.xi t
  have hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have hstep : ∀ k, Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta k =
      ((Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).1 * (_root_.GlobalTheory.Fam.pk_z W).xi t,
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta k).2 * (_root_.GlobalTheory.Fam.pk_z W).xi t) := by
    intro k
    unfold Lift.chrStep
    split_ifs <;> simp [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_right_comm]
  have hpow : ∀ x, (_root_.GlobalTheory.Fam.pk_z W).xi t x ^ n = 1 := pow_eq_one_of_chrEq hxi hn
  have hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (_root_.GlobalTheory.Fam.pk_z W).xi t x = 1 := eq_one_of_finPart hxi hn0 hn
  choose xr hxr using fun k => GlobalTheory.RecDict.exists_isDetRoot D (Yc D k) (f.g.b k)
  obtain ⟨xT, hxT⟩ := GlobalTheory.RecDict.exists_isDetRoot D D.sp.X' f.g.bT
  let w : ℕ → Circle := fun k => if k + 1 < D.R.m then ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (xr (k + 1))
    else ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr k))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT
  refine ⟨fun k => (w k : ℂ), ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨n, hn0, ?_⟩
    have h1 : w k ^ n = 1 := by
      simp only [w]
      split_ifs <;> rw [mul_pow, inv_pow, hpow, hpow, inv_one, one_mul]
    have := congrArg (fun z : Circle => (z : ℂ)) h1
    simpa using this
  · intro j hj _ _ a ha a' ha' g hg
    have hW0 := hc.chain.ωY W.P.A3.A.μ0 j hj
    have hWt := hc.chain.ωY t j hj
    rw [hstep] at hWt
    obtain ⟨z, hz⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D j) a
    obtain ⟨y, hy1, hy⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a ha z hz
    obtain ⟨z', hz'⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D (j + 1)) a'
    obtain ⟨y', hy1', hy'⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a' ha' z' hz'
    rw [twist_eq hW0 hWt (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy (hxr j))
      (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy' (hxr (j + 1))) hg]
    have e : ((_root_.GlobalTheory.Fam.pk_z W).xi t (y * xr j))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t (y' * xr (j + 1)) = w j := by
      simp only [w, if_pos hj, map_mul, hinf _ hy1, hinf _ hy1', one_mul]
    rw [e]
  · intro j h g hg
    have hW0 := isWeil_rec (idx_top h) _ (hc.chain.ωX W.P.A3.A.μ0)
    have hWt := isWeil_rec (idx_top h) _ (hc.chain.ωX t)
    rw [hstep] at hWt
    have e := twist_eq hW0 hWt (hxr (j + 1)) hxT hg
    have hw : w (j + 1) = ((_root_.GlobalTheory.Fam.pk_z W).xi t (xr (j + 1)))⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).xi t xT := by
      simp only [w]
      rw [if_neg (by omega)]
    show _ = ((w (j + 1) : Circle) : ℂ) • _
    rw [hw]
    exact e
  · intro j
    refine ⟨n, hn0, ?_⟩
    have hν : (_root_.GlobalTheory.Fam.pk_z W).xi t ^ n = 1 := MonoidHom.ext fun x => by simpa using hpow x
    simp only [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_one, mul_pow, hν]
end
end
