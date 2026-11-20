import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

/- English proof (translation)
Use `choose ψ hψ using h`. Apply the tactic sequence `refine ⟨⟨⟨⟨ψ, hb ?_⟩, fun x y => hb ?_⟩, hb ?_, fun x y => hb ?_⟩, RingHom.ext fun r => hψ r⟩ <;>`. Simplify using `[hψ]`.
-/
theorem exists_restrict_ringHom {R K V F : Type} [CommRing R] [CommRing K] [CommRing V] [CommRing F]
    (a : R →+* K) (b : V →+* F) (hb : Function.Injective b) (i : K →+* F)
    (h : ∀ r : R, i (a r) ∈ Set.range b) : ∃ ψ : R →+* V, b.comp ψ = i.comp a := by
  choose ψ hψ using h
  refine ⟨⟨⟨⟨ψ, hb ?_⟩, fun x y => hb ?_⟩, hb ?_, fun x y => hb ?_⟩, RingHom.ext fun r => hψ r⟩ <;>
    simp [hψ]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ z p T iK M hT A hA`. Take `⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hR, ⟨hfib, -⟩, -, hv⟩` from `hA`. Establish `hinj : Function.Injective (algebraMap T.V T.Fr)` using `IsFractionRing.injective _ _`. Take `⟨ψ, hψ⟩` from `exists_restrict_ringHom (algebraMap R z.K) (algebraMap T.V T.Fr) hinj iK (fun r => (hT _).2 ((hR _).1 ⟨r, rfl⟩))`. Establish `hρψ : M.ρ = ψ.comp ρ`.

Use `RingHom.ext fun x => hinj ?_` and prove the remaining obligations. Establish `h₁` using `RingHom.congr_fun M.hρ x`. Establish `h₂` using `RingHom.congr_fun hψ (ρ x)`. Establish `h₃` using `RingHom.congr_fun hρ x`. Simplify using `only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢`.

Rewrite using `[h₁, h₂, h₃]`. Establish `hp : IsGrpPullback xR.P.A z.B.t.G (spMap ρ) φR` using `hfib`. Establish `e : spMap M.ρ = spMap ψ ≫ spMap ρ` using `by rw [hρψ]; exact spMap_comp ρ ψ`. Establish `hn : IsGrpPullback M.G.t.G z.B.t.G (spMap M.ρ) M.n.φ` using `M.n.cart`. Establish `w : M.n.φ ≫ z.B.t.G.hom = (M.G.t.G.hom ≫ spMap ψ) ≫ spMap ρ` using `by rw [hn.1.w, e, Category.assoc]`.

Establish `hq : IsGrpPullback M.G.t.G xR.P.A (spMap ψ) (hp.1.lift _ _ w)` using `IsGrpPullback.cancel hp (hn.congr e (hp.1.lift_fst _ _ w).symm) (hp.1.lift_snd _ _ w)`. Use `xR.P.isAb.comm` as an intermediate fact. Take `⟨v', hb, hv'⟩` from `GlobalTheory.exists_isLieBasis_baseChange R T.V ψ _ _ _ hq xR.P.isAb.smooth _ xR.v xR.basis`. Establish `hb' : ∀ (k : ℕ) (hk : xR.P.g = k), IsLieBasis fun i : Fin k => v' (i.cast hk.symm)`. Introduce and unpack `k rfl`.

Conclude with `hb`. Use `⟨fun k => v' (k.cast hg.symm), hb' _ hg, fun k => ?_⟩` and prove the remaining obligations. Take `⟨wK, hw, hw'⟩` from `hv k`. Use `⟨wK, hw, ?_⟩` and prove the remaining obligations. Establish `ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (Chart.dualMapR ψ) = (Formalism.L2.Pj.dualMap iK).comp (Formalism.L2.Pj.dualMap (algebraMap R z.K))`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `h₁` using `RingHom.congr_fun hψ x.fst`. Establish `h₂` using `RingHom.congr_fun hψ x.snd`. Simplify using `only [RingHom.comp_apply] at h₁ h₂`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations.

Simplify `h₁` using `[Formalism.L2.Pj.dualMap, Chart.dualMapR]`. Simplify using `only [Formalism.L2.Pj.dualMap, Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]`. Conclude with `h₂`. Establish `es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Chart.dualMapR ψ) = spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap R z.K))`. Rewrite using `[← spMap_comp, ← spMap_comp, ed]`.

Establish `e₁ : (v' (k.cast hg.symm)).left ≫ M.n.φ = spMap (Chart.dualMapR ψ) ≫ (xR.v (k.cast hg.symm)).left ≫ φR`. Rewrite using `[← Category.assoc, ← hv', Category.assoc, hp.1.lift_fst]`. Conclude with `(congrArg (_ ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) es).trans <| (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw'.symm)`.
-/
theorem exists_isLieBasis_locMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A → ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ wK.left ≫ z.m'.φ := by
  intro E _ _ _ H Dw l Xo c _ z p T iK M hT A hA
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hR, ⟨hfib, -⟩, -, hv⟩ := hA
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ⟩ := exists_restrict_ringHom (algebraMap R z.K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hT _).2 ((hR _).1 ⟨r, rfl⟩))
  have hρψ : M.ρ = ψ.comp ρ := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun M.hρ x
    have h₂ := RingHom.congr_fun hψ (ρ x)
    have h₃ := RingHom.congr_fun hρ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  have hp : IsGrpPullback xR.P.A z.B.t.G (spMap ρ) φR := hfib
  have e : spMap M.ρ = spMap ψ ≫ spMap ρ := by rw [hρψ]; exact spMap_comp ρ ψ
  have hn : IsGrpPullback M.G.t.G z.B.t.G (spMap M.ρ) M.n.φ := M.n.cart
  have w : M.n.φ ≫ z.B.t.G.hom = (M.G.t.G.hom ≫ spMap ψ) ≫ spMap ρ := by rw [hn.1.w, e, Category.assoc]
  have hq : IsGrpPullback M.G.t.G xR.P.A (spMap ψ) (hp.1.lift _ _ w) :=
    IsGrpPullback.cancel hp (hn.congr e (hp.1.lift_fst _ _ w).symm) (hp.1.lift_snd _ _ w)
  have := xR.P.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ _ _ _ hq xR.P.isAb.smooth _ xR.v xR.basis
  have hb' : ∀ (k : ℕ) (hk : xR.P.g = k), IsLieBasis fun i : Fin k => v' (i.cast hk.symm) := by
    rintro k rfl
    exact hb
  refine ⟨fun k => v' (k.cast hg.symm), hb' _ hg, fun k => ?_⟩
  obtain ⟨wK, hw, hw'⟩ := hv k
  refine ⟨wK, hw, ?_⟩
  have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (Chart.dualMapR ψ) =
      (Formalism.L2.Pj.dualMap iK).comp (Formalism.L2.Pj.dualMap (algebraMap R z.K)) := by
    refine RingHom.ext fun x => ?_
    have h₁ := RingHom.congr_fun hψ x.fst
    have h₂ := RingHom.congr_fun hψ x.snd
    simp only [RingHom.comp_apply] at h₁ h₂
    refine TrivSqZeroExt.ext ?_ ?_
    · simpa [Formalism.L2.Pj.dualMap, Chart.dualMapR] using h₁
    · simp only [Formalism.L2.Pj.dualMap, Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact h₂
  have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Chart.dualMapR ψ) =
      spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap R z.K)) := by
    rw [← spMap_comp, ← spMap_comp, ed]
  have e₁ : (v' (k.cast hg.symm)).left ≫ M.n.φ =
      spMap (Chart.dualMapR ψ) ≫ (xR.v (k.cast hg.symm)).left ≫ φR := by
    rw [← Category.assoc, ← hv', Category.assoc, hp.1.lift_fst]
  exact (congrArg (_ ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) es).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw'.symm)

end GlobalTheory.LamT
