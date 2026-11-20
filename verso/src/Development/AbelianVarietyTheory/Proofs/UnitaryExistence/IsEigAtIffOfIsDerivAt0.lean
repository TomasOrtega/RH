import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerivEig

open GlobalTheory.HolHom

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

/- English proof (translation)
Simplify using `[epsMul]`.
-/
theorem fst_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.fst (epsMul s x) = x.fst := by
  simp [epsMul]

/- English proof (translation)
Simplify using `[epsMul]`.
-/
theorem snd_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.snd (epsMul s x) = s * x.snd := by
  simp [epsMul]

/- English proof (translation)
Use `⟨?_, fun U hU f => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← h.1]`. Use `congr 2`. Use `ext1`. Conclude with `RingHom.ext fun x => fst_epsMul s x`.

Rewrite using `[valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), snd_epsMul, h.2 U hU, map_smul, smul_eq_mul]`.
-/
theorem isDerivAt_epsMul {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt c z w v)
    (s : ℂ) : HolHom.IsDerivAt c z (s • w) (spMap (epsMul s) ≫ v) := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← h.1]
    congr 2
    ext1
    exact RingHom.ext fun x => fst_epsMul s x
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), snd_epsMul, h.2 U hU, map_smul, smul_eq_mul]

/- English proof (translation)
Establish `h0 : c (L 0) = c 0` using `by rw [map_zero]`. Use `⟨h.1.trans h0, fun U hU f => ?_⟩` and prove the remaining obligations. Rewrite using `[h.2 U (by beta_reduce; rw [h0]; exact hU) f]`. Establish `h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0)`. Rewrite using `[map_zero]`.

Conclude with `((hc U hU).2 f).hasFDerivAt`. Conclude with `congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv`.
-/
theorem isDerivAt_of_comp_linear {c : V → (Sp ℂ ⟶ X)} (hc : HolAt c 0) (L : V →L[ℂ] V) {w : V}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt (fun t => c (L t)) 0 w v) : HolHom.IsDerivAt c 0 (L w) v := by
  have h0 : c (L 0) = c 0 := by rw [map_zero]
  refine ⟨h.1.trans h0, fun U hU f => ?_⟩
  rw [h.2 U (by beta_reduce; rw [h0]; exact hU) f]
  have h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((hc U hU).2 f).hasFDerivAt
  exact congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv

end General

/- English proof (translation)
Use `IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun a => ?_)` and prove the remaining obligations. Conclude with `congrArg Subtype.val (σ.injective (h a))`.
-/
theorem eq_of_relab_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) {τ τ' : E →+* ℂ}
    (h : ∀ a : 𝓞 E, relab c σ τ (a : E) = relab c σ τ' (a : E)) : τ = τ' := by
  refine IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun a => ?_)
  exact congrArg Subtype.val (σ.injective (h a))

end GlobalTheory.DerivEig

open GlobalTheory.HolHom GlobalTheory.DerivEig in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ g e F k P hP w v τ hv`. Establish `hhol : HolAt (fun z => (F.ex k P z).left) 0` using `holAt_of_isHolTo (isHolTo_ex F k hP) (Set.mem_univ 0)`. Establish `hv'` using `(isDerivAt0_iff _ _ _).1 hv`. Establish `hact : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (fun j => relab c σ (e j).1 (a : E) * w j) (v ≫ (Xo.univ.t.act.act a).left)`. Introduce `a`.

Set `L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)` to `ContinuousLinearMap.pi fun j => relab c σ (e j).1 (a : E) • ContinuousLinearMap.proj j`. Establish `h1` using `hv'.comp (Xo.univ.t.act.act a).left`. Establish `h2 : (fun t => (F.ex k P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (F.ex k P (L t)).left`. Use function extensionality and compare the values at `t`. Rewrite using `[← Over.comp_left, ← F.ex_lin k P hP a t]`.

Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Conclude with `isDerivAt_of_comp_linear hhol L h1`. Establish `hsc : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w) (spMap (epsMul (algebraMap c.F (CAt σ) (embK c τ a))) ≫ v)` using `fun a => isDerivAt_epsMul hv' _`. Prove the components needed by the constructor for the conclusion.

Introduce `h j hj`. Use `eq_of_relab_eq c σ fun a => ?_` and prove the remaining obligations. Establish `h1` using `hact a`. Establish `h2 : HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w) (v ≫ (Xo.univ.t.act.act a).left)` using `Eq.mpr (congrArg (HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)) (h a)) (hsc a)`. Establish `h3` using `eq_of_forall_fderiv_eq hhol (F.ex_diff k P hP).2 fun U hU f => (h1.2 U hU f).symm.trans (h2.2 U hU f)`.

Conclude with `mul_right_cancel₀ hj (congrFun h3 j)`. Introduce `h a`. Establish `h1` using `hact a`. Establish `h3 : (fun j => relab c σ (e j).1 (a : E) * w j) = relab c σ τ (a : E) • w`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : w j = 0`. Simplify using `[hj]`. Rewrite using `[h j hj]`. Both sides reduce to the same expression. Rewrite `h1` using `[h3]`.

Conclude with `h1.unique (hsc a)`.
-/
theorem GlobalTheory.isEigAt_iff_of_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∀ (w : Fin g → ℂ) (v : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)) (τ : E →+* ℂ), IsDerivAt0 (fun z => (F.ex k P z).left) w v → (IsEigAt c τ v ↔ ∀ j, w j ≠ 0 → (e j).1 = τ) := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP w v τ hv
  have hhol : HolAt (fun z => (F.ex k P z).left) 0 := holAt_of_isHolTo (isHolTo_ex F k hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  have hact : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (fun j => relab c σ (e j).1 (a : E) * w j) (v ≫ (Xo.univ.t.act.act a).left) := by
    intro a
    let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
      ContinuousLinearMap.pi fun j => relab c σ (e j).1 (a : E) • ContinuousLinearMap.proj j
    have h1 := hv'.comp (Xo.univ.t.act.act a).left
    have h2 : (fun t => (F.ex k P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (F.ex k P (L t)).left := by
      funext t
      rw [← Over.comp_left, ← F.ex_lin k P hP a t]
      rfl
    rw [h2] at h1
    exact isDerivAt_of_comp_linear hhol L h1
  have hsc : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (relab c σ τ (a : E) • w) (spMap (epsMul (algebraMap c.F (CAt σ) (embK c τ a))) ≫ v) :=
    fun a => isDerivAt_epsMul hv' _
  constructor
  · intro h j hj
    refine eq_of_relab_eq c σ fun a => ?_
    have h1 := hact a
    have h2 : HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)
        (v ≫ (Xo.univ.t.act.act a).left) :=
      Eq.mpr (congrArg (HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)) (h a)) (hsc a)
    have h3 := eq_of_forall_fderiv_eq hhol (F.ex_diff k P hP).2 fun U hU f =>
      (h1.2 U hU f).symm.trans (h2.2 U hU f)
    exact mul_right_cancel₀ hj (congrFun h3 j)
  · intro h a
    have h1 := hact a
    have h3 : (fun j => relab c σ (e j).1 (a : E) * w j) = relab c σ τ (a : E) • w := by
      funext j
      by_cases hj : w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
    rw [h3] at h1
    exact h1.unique (hsc a)
