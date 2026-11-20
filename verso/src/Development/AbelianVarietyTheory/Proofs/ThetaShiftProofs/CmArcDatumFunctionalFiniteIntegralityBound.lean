import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.AlgebraMapArcSInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisationStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section Lines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
  {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)} {th : a.D₀.P.L.Sec}
  {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩` from `s.good`. Conclude with `h.1`.
-/
theorem CMIn.fin_Tl_ne_zero (s : CMIn a e th jj n' La c₁) : s.Tl.I ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := s.good
  exact h.1

/- English proof (translation)
Use `letI := H.starRing`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩` from `s.good`. Unfold `CMIn.line`. Consider the cases of `s.kind τ k with`. Consider the case `none => exact one_ne_zero`.

Consider the case `some m`. Establish `h` using `s.L_good.2.2.2 m`. Use `show (s.L.ℓ m).I ≠ 0`. Use `revert h`. Consider the cases of `s.L.src m with`.

Consider the case `inl q => intro h`. Rewrite using `[show s.L.ℓ m = _ from h]`. Conclude with `(h1 q.2).1.1`. Consider the case `inr q => intro h`. Rewrite using `[show s.L.ℓ m = _ from h]`.

Conclude with `(h2 q.2).1.1`.
-/
theorem CMIn.fin_line_ne_zero (s : CMIn a e th jj n' La c₁) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    (s.line τ k).I ≠ 0 := by
  letI := H.starRing
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := s.good
  unfold CMIn.line
  cases s.kind τ k with
  | none => exact one_ne_zero
  | some m =>
    have h := s.L_good.2.2.2 m
    show (s.L.ℓ m).I ≠ 0
    revert h
    cases s.L.src m with
    | inl q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h1 q.2).1.1
    | inr q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h2 q.2).1.1

/- English proof (translation)
Establish `hT` using `s.fin_Tl_ne_zero`. Establish `hL : ∀ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v ≠ 0` using `fun v => pow_ne_zero _ (s.fin_line_ne_zero _ _)`. Use `show FractionalIdeal.count K₁ w ((s.Tl.I⁻¹) ^ n * (∏ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v)⁻¹) = _`. Rewrite using `[FractionalIdeal.count_mul K₁ w (pow_ne_zero _ (inv_ne_zero hT)) (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hL v)), FractionalIdeal.count_pow, FractionalIdeal.count_inv, FractionalIdeal.count_inv, FractionalIdeal.count_prod K₁ w _ _ (fun v _ => hL v)]`. Use `congr 1`.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `symm`. Use `Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_) |>.trans ?_` and prove the remaining obligations. Rewrite using `[Finsupp.notMem_support_iff.mp hx]`. Simplify using the standard rewrite rules.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.count_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CMIn.fin_count_valLine (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ)
    (w : HeightOneSpectrum (𝓞 K₁)) :
    FractionalIdeal.count K₁ w (s.valLine mo n).I =
      (n : ℤ) * (-FractionalIdeal.count K₁ w s.Tl.I) +
        ∑ x ∈ mo.support, (mo x : ℤ) * (-FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) := by
  classical
  have hT := s.fin_Tl_ne_zero
  have hL : ∀ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v ≠ 0 := fun v => pow_ne_zero _ (s.fin_line_ne_zero _ _)
  show FractionalIdeal.count K₁ w ((s.Tl.I⁻¹) ^ n * (∏ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v)⁻¹) = _
  rw [FractionalIdeal.count_mul K₁ w (pow_ne_zero _ (inv_ne_zero hT))
      (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hL v)),
    FractionalIdeal.count_pow, FractionalIdeal.count_inv, FractionalIdeal.count_inv,
    FractionalIdeal.count_prod K₁ w _ _ (fun v _ => hL v)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_) |>.trans ?_
  · rw [Finsupp.notMem_support_iff.mp hx]; simp
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [FractionalIdeal.count_pow]; ring

end Lines

/- English proof (translation)
Introduce `hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS _ la w hlw a' n F hF hne`. Take `⟨Z, gm, lam, A, Bm, ⟨hg0, hg⟩, hlam, ⟨hAB, hA⟩, hbd⟩` from `GlobalTheory.T.localArcIntegrality_of_cmNormalisedTrivialisation hK E H Dw l Xo c K₁ d n' La c₁ s hM hS la w hlw a' n`. Take `⟨P, hPe, hPh⟩` from `GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d a' n F hF.1`. Use `set m : ℕ := w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la with hm`. Establish `hC1 : (1 : ℝ) ≤ Z.r ^ (-(m : ℤ))`.

Rewrite using `[zpow_neg, zpow_natCast]`. Conclude with `(one_le_inv₀ (pow_pos Z.r_pos _)).mpr (pow_le_one₀ Z.r_pos.le Z.r_lt.le)`. Establish `hbd'` using `hbd F hF`. Rewrite `hbd'` using `[← hPe, FinPf.arcNum_algebraMap]`. Establish `key` using `FinKey.coeff_bound finCore_holds basisChange_holds (GlobalTheory.ArcQ.FinSite.«ι» Z) Z.K₀ Z.res Z.S Z.S_disc Z.S_dense Z.S_units P (absA Dw a') hPh n gm hg0 lam (fun τ k => (hlam τ k).1) A Bm hAB _ hC1 hA hbd' d.μ d.jj`.

Establish `hcf : cfOf d.yF d.μ d.jj F = (P.coeff d.μ).coeff d.jj`. Rewrite using `[cfOf, ← hPe, FinPf.arcNum_algebraMap]`. Rewrite `hne`, the goal using `[hcf]`. Rewrite `key` using `[GlobalTheory.ArcQ.FinSite.«norm_ι» Z _ hne, hg]`. Simplify using `only [Finsupp.prod, (hlam _ _).2] at key`.

Establish `hz` using `FinPf.zpow_bound Z.r Z.r_pos Z.r_lt _ _ n (absA Dw a') m d.μ.support d.μ (fun x => -FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) key`. Rewrite using `[s.fin_count_valLine]`. Simplify using `only [beOf, hm] at hz ⊢`. Move the coercions through the operations in `at hz ⊢`. Use polynomial arithmetic with `[hz]`.
-/
theorem cfOf_fin_bound : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → 1 ≤ La → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ intAt Xo c a' n la, cfOf d.yF d.μ d.jj F ≠ 0 → -((w.asIdeal.ramificationIdx (𝓞 c.F) : ℝ) * beOf E n' (absA Dw a') la) ≤ (ordAt w (cfOf d.yF d.μ d.jj F) : ℝ) - (FractionalIdeal.count K₁ w (s.valLine d.μ n).I : ℝ) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS _ la w hlw a' n F hF hne
  obtain ⟨Z, gm, lam, A, Bm, ⟨hg0, hg⟩, hlam, ⟨hAB, hA⟩, hbd⟩ :=
    GlobalTheory.T.localArcIntegrality_of_cmNormalisedTrivialisation hK E H Dw l Xo c K₁ d n' La c₁ s hM hS la w hlw a' n
  obtain ⟨P, hPe, hPh⟩ := GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c)
    K₁ d a' n F hF.1
  set m : ℕ := w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la with hm
  have hC1 : (1 : ℝ) ≤ Z.r ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos Z.r_pos _)).mpr (pow_le_one₀ Z.r_pos.le Z.r_lt.le)
  have hbd' := hbd F hF
  rw [← hPe, FinPf.arcNum_algebraMap] at hbd'
  have key := FinKey.coeff_bound finCore_holds basisChange_holds (GlobalTheory.ArcQ.FinSite.«ι» Z) Z.K₀ Z.res Z.S Z.S_disc Z.S_dense
    Z.S_units P (absA Dw a') hPh n gm hg0 lam (fun τ k => (hlam τ k).1) A Bm hAB _ hC1 hA hbd' d.μ d.jj
  have hcf : cfOf d.yF d.μ d.jj F = (P.coeff d.μ).coeff d.jj := by
    rw [cfOf, ← hPe, FinPf.arcNum_algebraMap]
  rw [hcf] at hne ⊢
  rw [GlobalTheory.ArcQ.FinSite.«norm_ι» Z _ hne, hg] at key
  simp only [Finsupp.prod, (hlam _ _).2] at key
  have hz := FinPf.zpow_bound Z.r Z.r_pos Z.r_lt _ _ n (absA Dw a') m d.μ.support d.μ
    (fun x => -FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) key
  rw [s.fin_count_valLine]
  simp only [beOf, hm] at hz ⊢
  push_cast at hz ⊢
  nlinarith [hz]

end GlobalTheory.ArcCM
