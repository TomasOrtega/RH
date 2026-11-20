import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.RungJac

/- English proof (translation)
Establish `hdesc` using `GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)`. Take `⟨omA, hA⟩` from `(hdesc ψ V W χV χW om h).1 V₀ ρ dV`. Take `⟨om₀, h₀⟩` from `(hdesc ψ V₀ W χV χW omA hA).2 W₀ σ dW`. Take `⟨vS⟩` from `GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ`. Take `⟨vT⟩` from `GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank`.

Take `⟨vU⟩` from `GlobalTheory.Unf.VolExist.nonempty_volU D ρ`. Conclude with `⟨{ χV := χV, χW := χW, om := om, om₀ := om₀, weil := h, weil₀ := h₀, vW := vW, vS := vS, vT := vT, vU := vU }, rfl, rfl, rfl, rfl⟩`.
-/
theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.om = om ∧ s.χV = χV ∧ s.χW = χW ∧ s.vW = vW := by

  have hdesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨omA, hA⟩ := (hdesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hdesc ψ V₀ W χV χW omA hA).2 W₀ σ dW

  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨{ χV := χV, χW := χW, om := om, om₀ := om₀, weil := h, weil₀ := h₀, vW := vW, vS := vS, vT := vT, vU := vU },
    rfl, rfl, rfl, rfl⟩

/- English proof (translation)
Use `⟨fun γ hγ g => ?_, continuous_star.comp hf.2.1, fun N => ?_⟩` and prove the remaining obligations. Use `show star (f (γ * g)) = star (f g)`. Rewrite using `[hf.1 γ hγ g]`. Take `⟨C, hC⟩` from `hf.2.2 N`. Conclude with `⟨C, fun g => by simpa only [Pi.star_apply, norm_star] using hC g⟩`.
-/
private theorem rapidDec_star' {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : RapidDec V f) : RapidDec V (star f) := by
  refine ⟨fun γ hγ g => ?_, continuous_star.comp hf.2.1, fun N => ?_⟩
  · show star (f (γ * g)) = star (f g)
    rw [hf.1 γ hγ g]
  · obtain ⟨C, hC⟩ := hf.2.2 N
    exact ⟨C, fun g => by simpa only [Pi.star_apply, norm_star] using hC g⟩

/- English proof (translation)
Establish `e : (χ' : (AE D)ˣ → Circle) = fun x => (χ x)⁻¹ * (χ * χ') x`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `h.1.inv.mul h'.1`. Establish `hx` using `h'.2 x`. Rewrite `hx` using `[MonoidHom.mul_apply, h.2 x, one_mul]`. Conclude with `hx`.
-/
private theorem isHeckeChar_of_isHeckeChar_mul {D : D7} {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ)
    (h' : IsHeckeChar D (χ * χ')) : IsHeckeChar D χ' := by
  have e : (χ' : (AE D)ˣ → Circle) = fun x => (χ x)⁻¹ * (χ * χ') x := by
    funext x
    simp
  refine ⟨?_, fun x => ?_⟩
  · rw [e]
    exact h.1.inv.mul h'.1
  · have hx := h'.2 x
    rw [MonoidHom.mul_apply, h.2 x, one_mul] at hx
    exact hx

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hFock hFix D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h h' hB`. Take `⟨ρ, Φ, hne⟩` from `hB`. Establish `hi : 2 * k + 2 < D.R.m` using `by omega`. Take `⟨c1, c2, -, c4, c5, c6, c7, c8, c9h, c9f⟩` from `GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 2) hi`. Take `⟨c4a, c4b⟩` from `c4 ⟨k + 1, by omega⟩`.

Rewrite `c1` using `[c4a, c4b]`. Establish `hex` using `GlobalTheory.WeilDatumExistence.weilDatumExists D`. Establish `hc2` using `((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c2⟩`. Establish `hc1` using `((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c1⟩`. Establish `hEta : IsHeckeChar D L.eta` using `isHeckeChar_of_isHeckeChar_mul hc2.2.1 hc1.2.2.1`.

Choose the witnesses or unpack the hypotheses as in `⟨omz, hz⟩ : ∃ omz : Om (G.V (.core (2 * k + 2 + 1))) (negSp F.Lz), IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta omz := by`. Use `hex _ _ W.ψ _ _ W.ψ_std hc2.2.1 hEta hc2.2.2.2.1 ?_` and prove the remaining obligations. Use `show ResEta D L.eta F.Lz.rank`. Rewrite using `[F.rk]`. Conclude with `GlobalTheory.HeckeCharacterRestriction.resEta_eta hL`.

Take `⟨s, hs_om, hs_χV, hs_χW, hs_vW⟩` from `exists_step (F.dJ (k + 1) h) (F.dB k h') c1 ⟨M.ν (.grid (2 * k + 2) 0), M.fd (.grid (2 * k + 2) 0), c9h, c9f⟩`. Take `⟨𝒮, Γ₀, hLoc, hRow, hBox⟩` from `hGood.fb k h h' s hs_om`. Take `⟨f, hf, hΨi⟩` from `hΨ.2 (2 * k + 2) hi`. Take `⟨Φ₀, hΦ₀, hΦ₀ne⟩` from `hGood.lineNe (k + 1) h`. Establish `hVf` using `(c5 f).1 hf`.

Establish `hRφ : RapidDec _ (star (Ψ (2 * k + 2 + 1)))` using `rapidDec_star' (hΨ.1 _ (by omega))`. Establish `hRG : RapidDec _ (star (part W M ρ Φ u (2 * k + 2) h'))` using `rapidDec_star' (hu ρ Φ _ _)`. Establish `hK : ∀ x ∈ lev G (.grid (2 * k + 2) 0), ∀ g, star (part W M ρ Φ u (2 * k + 2) h') (g * x) = star (part W M ρ Φ u (2 * k + 2) h') g` using `fun x hx g => congrArg star (hFix D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k + 1) h' x hx g)`. Establish `hper : (F.bes v k h').per W.ψ (liftT (omCore W (2 * k + 2)) (v (2 * k + 2 + 1)).μ (v (2 * k + 2 + 1)).𝓕 (star (Ψ (2 * k + 2 + 1))) (star f)) (star (part W M ρ Φ u (2 * k + 2) h')) ≠ 0`. Rewrite using `[← c6 v f (Ψ (2 * k + 2 + 1)), ← hΨi]`.

Conclude with `hne`. Take `⟨Φ', hΦ'𝒮, hΦ'ne⟩` from `GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift D W.ψ k (F.jac v (k + 1) h) (F.bes v k h') s 𝒮 Γ₀ _ hLoc (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta (omCore W (2 * k + 2)) omz hs_χW (by rw [hs_χV]; exact c2) (by rw [hs_χV]; exact hz) _ _ hRφ hRG hK (star f) Φ₀ hVf.1 …`. Establish `hTame` using `(GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ s.vW (star (part W M ρ Φ u (2 * k + 2) h')) hRG).2 (k + 1) (F.jac v (k + 1) h) _ _ s.om s.weil (negSp F.Lz) (F.ζ (k + 1)) _ _ omz hz (star (Ψ (2 * k + 2 + 1))) Φ₀ hRφ hΦ₀.1`. Establish `hFk` using `hFock D hD T L μ0 hL sc G W M hM ⟨2 * k + 2, hi⟩ _ hTame`. Choose the witnesses or unpack the hypotheses as in `⟨κ, P, hκP⟩ : ∃ κ P, (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1))) (s.lift (star (part W M ρ Φ u (2 * k + 2) h')) (star (W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P))) Φ₀ ≠ 0 := by`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hΦ'ne (hFk hall Φ' (hRow Φ' hΦ'𝒮))`. Establish `hpart : part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2) hi.le = part W M ρ Φ u (2 * k + 2) hi.le`. Use `(c8 ρ Φ _ _ u fun j hj => ?_).symm` and prove the remaining obligations.

Establish `hj' : j ≠ ⟨2 * k + 2, hi⟩` using `fun e => by`. Rewrite `hj` using `[e]`. Conclude with `lt_irrefl _ hj`. Conclude with `⟨(Function.update_of_ne hj' P ρ).symm, (Function.update_of_ne hj' κ Φ).symm⟩`. Establish `hdat : W.datum (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) ⟨2 * k + 2, hi⟩ = W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P`.

Simplify using `only [GridData.Weil.datum, Function.update_self]`. Establish `hlift` using `c7 (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u`. Rewrite `hlift` using `[hpart, hdat]`. Establish `e2 : ∀ G0 X, s.lift G0 X = liftS (omRow W (2 * k + 2)) (M.ν (.grid (2 * k + 2) 0)) (M.fd (.grid (2 * k + 2) 0)) G0 X`. Introduce `G0 X`.

Use `show liftS s.om s.vW.μ s.vW.𝓕 G0 X = _`. Rewrite using `[hs_om, hs_vW]`. Rewrite `hκP` using `[e2]`. Use `⟨_, omz, hz, Function.update ρ ⟨2 * k + 2, hi⟩ P, Function.update Φ ⟨2 * k + 2, hi⟩ κ, Φ₀, hΦ₀, ?_⟩` and prove the remaining obligations. Establish `key : (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1))) (star (part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2 + 1) hi)) Φ₀ ≠ 0`.

Rewrite using `[hlift]`. Conclude with `hκP`. Conclude with `key`.
-/
theorem rungJ : FockTot → PartFixed → RungJ := by
  intro hFock hFix D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h h' hB
  obtain ⟨ρ, Φ, hne⟩ := hB
  have hi : 2 * k + 2 < D.R.m := by omega

  obtain ⟨c1, c2, -, c4, c5, c6, c7, c8, c9h, c9f⟩ :=
    GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 2) hi
  obtain ⟨c4a, c4b⟩ := c4 ⟨k + 1, by omega⟩
  rw [c4a, c4b] at c1

  have hex := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hc2 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c2⟩
  have hc1 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c1⟩
  have hEta : IsHeckeChar D L.eta := isHeckeChar_of_isHeckeChar_mul hc2.2.1 hc1.2.2.1
  obtain ⟨omz, hz⟩ : ∃ omz : Om (G.V (.core (2 * k + 2 + 1))) (negSp F.Lz),
      IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta omz := by
    refine hex _ _ W.ψ _ _ W.ψ_std hc2.2.1 hEta hc2.2.2.2.1 ?_
    show ResEta D L.eta F.Lz.rank
    rw [F.rk]
    exact GlobalTheory.HeckeCharacterRestriction.resEta_eta hL

  obtain ⟨s, hs_om, hs_χV, hs_χW, hs_vW⟩ := exists_step (F.dJ (k + 1) h) (F.dB k h') c1
    ⟨M.ν (.grid (2 * k + 2) 0), M.fd (.grid (2 * k + 2) 0), c9h, c9f⟩
  obtain ⟨𝒮, Γ₀, hLoc, hRow, hBox⟩ := hGood.fb k h h' s hs_om

  obtain ⟨f, hf, hΨi⟩ := hΨ.2 (2 * k + 2) hi
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hGood.lineNe (k + 1) h
  have hVf := (c5 f).1 hf
  have hRφ : RapidDec _ (star (Ψ (2 * k + 2 + 1))) := rapidDec_star' (hΨ.1 _ (by omega))
  have hRG : RapidDec _ (star (part W M ρ Φ u (2 * k + 2) h')) := rapidDec_star' (hu ρ Φ _ _)
  have hK : ∀ x ∈ lev G (.grid (2 * k + 2) 0), ∀ g,
      star (part W M ρ Φ u (2 * k + 2) h') (g * x) = star (part W M ρ Φ u (2 * k + 2) h') g :=
    fun x hx g => congrArg star (hFix D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k + 1) h' x hx g)

  have hper : (F.bes v k h').per W.ψ
      (liftT (omCore W (2 * k + 2)) (v (2 * k + 2 + 1)).μ (v (2 * k + 2 + 1)).𝓕 (star (Ψ (2 * k + 2 + 1))) (star f))
      (star (part W M ρ Φ u (2 * k + 2) h')) ≠ 0 := by
    rw [← c6 v f (Ψ (2 * k + 2 + 1)), ← hΨi]
    exact hne

  obtain ⟨Φ', hΦ'𝒮, hΦ'ne⟩ := GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift D W.ψ k (F.jac v (k + 1) h) (F.bes v k h') s 𝒮 Γ₀ _ hLoc
    (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta (omCore W (2 * k + 2)) omz hs_χW (by rw [hs_χV]; exact c2)
    (by rw [hs_χV]; exact hz) _ _ hRφ hRG hK (star f) Φ₀ hVf.1 hΦ₀.1 hΦ₀ne (hBox _ _ hVf hΦ₀) hper

  have hTame := (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ s.vW (star (part W M ρ Φ u (2 * k + 2) h')) hRG).2 (k + 1)
    (F.jac v (k + 1) h) _ _ s.om s.weil (negSp F.Lz) (F.ζ (k + 1)) _ _ omz hz (star (Ψ (2 * k + 2 + 1))) Φ₀ hRφ hΦ₀.1
  have hFk := hFock D hD T L μ0 hL sc G W M hM ⟨2 * k + 2, hi⟩ _ hTame
  obtain ⟨κ, P, hκP⟩ : ∃ κ P, (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (s.lift (star (part W M ρ Φ u (2 * k + 2) h')) (star (W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P))) Φ₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hΦ'ne (hFk hall Φ' (hRow Φ' hΦ'𝒮))

  have hpart : part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2) hi.le =
      part W M ρ Φ u (2 * k + 2) hi.le := by
    refine (c8 ρ Φ _ _ u fun j hj => ?_).symm
    have hj' : j ≠ ⟨2 * k + 2, hi⟩ := fun e => by
      rw [e] at hj
      exact lt_irrefl _ hj
    exact ⟨(Function.update_of_ne hj' P ρ).symm, (Function.update_of_ne hj' κ Φ).symm⟩
  have hdat : W.datum (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) ⟨2 * k + 2, hi⟩ =
      W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P := by
    simp only [GridData.Weil.datum, Function.update_self]
  have hlift := c7 (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u
  rw [hpart, hdat] at hlift
  have e2 : ∀ G0 X, s.lift G0 X = liftS (omRow W (2 * k + 2)) (M.ν (.grid (2 * k + 2) 0)) (M.fd (.grid (2 * k + 2) 0)) G0 X := by
    intro G0 X
    show liftS s.om s.vW.μ s.vW.𝓕 G0 X = _
    rw [hs_om, hs_vW]
  rw [e2] at hκP
  refine ⟨_, omz, hz, Function.update ρ ⟨2 * k + 2, hi⟩ P, Function.update Φ ⟨2 * k + 2, hi⟩ κ, Φ₀, hΦ₀, ?_⟩
  have key : (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (star (part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2 + 1) hi)) Φ₀ ≠ 0 := by
    rw [hlift]
    exact hκP
  exact key

end GlobalTheory.Asc.RungJac

end
