import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointLift

open ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U W hσ hU hinj k Q hQ q hq`. Take `⟨k₁, x₁, t, hB⟩` from `hU.2.2.1 q`. Establish `hx₁ : (U.un k₁ x₁).x = W.F.u (W.ik k₁) (W.Pm k₁ x₁)` using `(W.lie k₁ x₁).1`. Establish `hk : k₁ = k` using `hinj (W.F.disj _ _ _ _ (W.period k₁ x₁) hQ (by rw [← hx₁, ← hB.1, hq]))`. Substitute `hk` using the available equality.

Take `⟨gam, h, hEF, -, -, hgh⟩` from `(W.F.fibre _ Q (W.Pm k₁ x₁) hQ (W.period k₁ x₁)).1 (by rw [hq, ← hx₁, hB.1])`. Set `φL : (W.F.Di (W.ik k₁)).La →ₗ[𝓞 E] (Fin r → E)` to `(U.X k₁).Λ.subtype ∘ₗ (W.φ k₁).toLinearMap`. Establish `hφi : Function.Injective φL` using `(U.X k₁).Λ.injective_subtype.comp (W.φ k₁).injective`. Establish `hrange : Set.range φL = ((U.X k₁).Λ : Set (Fin r → E))`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `(W.φ k₁ a).2`. Introduce `hv`. Conclude with `⟨(W.φ k₁).symm ⟨v, hv⟩, by simp [φL]⟩`.

Establish `hspan : Submodule.span E (Set.range φL) = ⊤` using `by rw [hrange]; exact (U.X k₁).Λ_span`. Establish `hcc : cc (-(U.X k₁).ξ0) = -(-(U.X k₁).ξ0)`. Establish `h0` using `(U.X k₁).ξ0_im`. Unfold `cc at h0 ⊢`. Rewrite using `[map_neg, h0]`.

Establish `hl : Function.Injective φL ∧ Submodule.span E (Set.range φL) = ⊤ ∧ (∀ a b, cc ((U.X k₁).Gm a b) = (U.X k₁).Gm b a) ∧ (U.X k₁).Gm.det ≠ 0 ∧ ∀ x y, (((W.F.Di (W.ik k₁)).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k₁).ξ0 * herm (U.X k₁).Gm (φL x) (φL y))` using `⟨hφi, hspan, (U.X k₁).Gm_herm, (U.X k₁).Gm_det, fun x y => W.iso k₁ x y⟩`. Apply the tactic sequence `obtain ⟨γ, hγh, hγφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k₁).ξ0) (U.X k₁).Gm φL φL gam hcc hl hl hEF`. Establish `hinv : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v` using `fun v => by`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `hinv' : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v` using `fun v => by`.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hγi : IsUStab (U.X k₁).Gm (U.X k₁).Λ γ⁻¹`. Use `⟨fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hγh, hinv', hinv']`. Take `⟨b, hb⟩ : v ∈ Set.range φL` from `by rw [hrange]; exact hv`.

Establish `e : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = φL (gam.symm b)`. Rewrite using `[← hb, ← LinearEquiv.apply_symm_apply gam b, hγφ, hinv, LinearEquiv.apply_symm_apply]`. Rewrite using `[e]`. Conclude with `(W.φ k₁ (gam.symm b)).2`. Take `⟨a, ha⟩ : _ ∈ Set.range φL` from `by rw [hrange]; exact hv`.

Establish `e : v = φL (gam a)` using `by rw [hγφ, ha, hinv']`. Rewrite using `[e]`. Conclude with `(W.φ k₁ (gam a)).2`. Set `x' : (U.X k₁).dom` to `⟨lact γ⁻¹ x₁.1, GlobalTheory.MajInv.lact_mem_dom _ hγi x₁.2⟩`. Establish `hPm : ∀ a, W.Pm k₁ x' a = W.Pm k₁ x₁ (gam a)`.

Introduce `a`. Use function extensionality and compare the values at `j`. Rewrite using `[W.Pm_eq, W.Pm_eq]`. Establish `e : (W.φ k₁ a : Fin r → E) = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (W.φ k₁ (gam a) : Fin r → E)`. Express the relevant statement in the definitionally equal form `φL a = _ *ᵥ φL (gam a)`.

Rewrite using `[hγφ, hinv]`. Rewrite using `[e]`. Conclude with `GlobalTheory.CongrOrbit.perFr_lact _ _ _ hγi.1 _ _ _`. Establish `hQx : ∀ a, W.Pm k₁ x' a = h (Q a)` using `fun a => by rw [hPm, hgh]`. Establish `hu : W.F.u (W.ik k₁) Q = W.F.u (W.ik k₁) (W.Pm k₁ x')` using `(W.F.fibre _ Q (W.Pm k₁ x') hQ (W.period k₁ x')).2 ⟨LinearEquiv.refl _ _, h, fun a b => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun a => hQx a⟩`.

Use `⟨x', by rw [(W.lie k₁ x').1, ← hu, hq], h.symm, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hQx, LinearEquiv.symm_apply_apply]`.
-/
theorem pm_lift_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  intro E _ _ _ H Dw l Xo c σ r U W hσ hU hinj k Q hQ q hq
  obtain ⟨k₁, x₁, t, hB⟩ := hU.2.2.1 q
  have hx₁ : (U.un k₁ x₁).x = W.F.u (W.ik k₁) (W.Pm k₁ x₁) := (W.lie k₁ x₁).1
  have hk : k₁ = k := hinj (W.F.disj _ _ _ _ (W.period k₁ x₁) hQ (by rw [← hx₁, ← hB.1, hq]))
  subst hk
  obtain ⟨gam, h, hEF, -, -, hgh⟩ := (W.F.fibre _ Q (W.Pm k₁ x₁) hQ (W.period k₁ x₁)).1
    (by rw [hq, ← hx₁, hB.1])
  let φL : (W.F.Di (W.ik k₁)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k₁).Λ.subtype ∘ₗ (W.φ k₁).toLinearMap
  have hφi : Function.Injective φL := (U.X k₁).Λ.injective_subtype.comp (W.φ k₁).injective
  have hrange : Set.range φL = ((U.X k₁).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k₁ a).2
    · intro hv
      exact ⟨(W.φ k₁).symm ⟨v, hv⟩, by simp [φL]⟩
  have hspan : Submodule.span E (Set.range φL) = ⊤ := by rw [hrange]; exact (U.X k₁).Λ_span
  have hcc : cc (-(U.X k₁).ξ0) = -(-(U.X k₁).ξ0) := by
    have h0 := (U.X k₁).ξ0_im
    unfold cc at h0 ⊢
    rw [map_neg, h0]
  have hl : Function.Injective φL ∧ Submodule.span E (Set.range φL) = ⊤ ∧
      (∀ a b, cc ((U.X k₁).Gm a b) = (U.X k₁).Gm b a) ∧ (U.X k₁).Gm.det ≠ 0 ∧
      ∀ x y, (((W.F.Di (W.ik k₁)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k₁).ξ0 * herm (U.X k₁).Gm (φL x) (φL y)) :=
    ⟨hφi, hspan, (U.X k₁).Gm_herm, (U.X k₁).Gm_det, fun x y => W.iso k₁ x y⟩
  obtain ⟨γ, hγh, hγφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k₁).ξ0) (U.X k₁).Gm φL φL gam
    hcc hl hl hEF
  have hinv : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hγi : IsUStab (U.X k₁).Gm (U.X k₁).Λ γ⁻¹ := by
    refine ⟨fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [← hγh, hinv', hinv']
    · obtain ⟨b, hb⟩ : v ∈ Set.range φL := by rw [hrange]; exact hv
      have e : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = φL (gam.symm b) := by
        rw [← hb, ← LinearEquiv.apply_symm_apply gam b, hγφ, hinv, LinearEquiv.apply_symm_apply]
      rw [e]
      exact (W.φ k₁ (gam.symm b)).2
    · obtain ⟨a, ha⟩ : _ ∈ Set.range φL := by rw [hrange]; exact hv
      have e : v = φL (gam a) := by rw [hγφ, ha, hinv']
      rw [e]
      exact (W.φ k₁ (gam a)).2
  let x' : (U.X k₁).dom := ⟨lact γ⁻¹ x₁.1, GlobalTheory.MajInv.lact_mem_dom _ hγi x₁.2⟩
  have hPm : ∀ a, W.Pm k₁ x' a = W.Pm k₁ x₁ (gam a) := by
    intro a
    funext j
    rw [W.Pm_eq, W.Pm_eq]
    have e : (W.φ k₁ a : Fin r → E) = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        (W.φ k₁ (gam a) : Fin r → E) := by
      change φL a = _ *ᵥ φL (gam a)
      rw [hγφ, hinv]
    rw [e]
    exact GlobalTheory.CongrOrbit.perFr_lact _ _ _ hγi.1 _ _ _
  have hQx : ∀ a, W.Pm k₁ x' a = h (Q a) := fun a => by rw [hPm, hgh]
  have hu : W.F.u (W.ik k₁) Q = W.F.u (W.ik k₁) (W.Pm k₁ x') :=
    (W.F.fibre _ Q (W.Pm k₁ x') hQ (W.period k₁ x')).2
      ⟨LinearEquiv.refl _ _, h, fun a b => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩,
        fun a => hQx a⟩
  refine ⟨x', by rw [(W.lie k₁ x').1, ← hu, hq], h.symm, fun a => ?_⟩
  rw [hQx, LinearEquiv.symm_apply_apply]

end GlobalTheory.PointLift
