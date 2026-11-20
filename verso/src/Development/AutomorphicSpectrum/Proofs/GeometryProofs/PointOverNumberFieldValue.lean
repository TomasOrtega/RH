import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceOfNotMemGenFibre

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LiesOver

open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

/- English proof (translation)
Take `⟨hz, t, rfl, rfl⟩` from `h`. Take `⟨_, t', rfl, rfl⟩` from `h'`. Conclude with `⟨hz, t + t', map_add _ _ _, map_add _ _ _⟩`.
-/
theorem valAt_add {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t + t', map_add _ _ _, map_add _ _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩`.
-/
theorem valAt_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {w : (Σ k, J k) → ℂ}

/- English proof (translation)
Simplify using `[evC, ArakelovGeometry.xpow, map_prod]`.
-/
theorem evC_xpow (w : (Σ k, J k) → ℂ) (c : ∀ k, J k) (e : K → ℕ) :
    evC w (ArakelovGeometry.xpow c e) = ∏ k, w ⟨k, c k⟩ ^ e k := by
  simp [evC, ArakelovGeometry.xpow, map_prod]

/- English proof (translation)
Establish `hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0` using `fun k => (hc k).ne_zero`. Establish `hW : ∀ δ : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0` using `fun δ => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc0 k)`. Establish `hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k = (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k` using `fun δ₁ δ₂ => by`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`.

Establish `hpowC : ∀ δ₁ δ₂ : K → ℕ, ∏ k, w ⟨k, c k⟩ ^ (δ₁ + δ₂) k = (∏ k, w ⟨k, c k⟩ ^ δ₁ k) * ∏ k, w ⟨k, c k⟩ ^ δ₂ k` using `fun δ₁ δ₂ => by`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Rewrite `hx` using `[chartRingZ]`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨⟨k, i⟩, rfl⟩` from `hx`. Use `⟨Pi.single k 1, MvPolynomial.X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_X, Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]`. Simplify using `[div_mul_cancel₀ _ (hy k)]`.

Take `⟨r, hr, e⟩` from `(hw.2 k (c k) (hc k)).2 i`. Establish `e1 : (∏ k', w ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k') = w ⟨k, c k⟩`. Rewrite using `[Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]`. Simplify using the standard rewrite rules. Establish `e2 : evC w (MvPolynomial.X ⟨k, i⟩ : MRing J) = w ⟨k, i⟩` using `by simp [evC]`.

Rewrite using `[e1, e2, e, mul_div_cancel_right₀ _ (hc0 k)]`. Conclude with `hr`. Consider the case `algebraMap r`. Use `⟨0, C r, isMultiHomog_C r, by simp, ?_⟩` and prove the remaining obligations. Establish `e : evC w (C r : MRing J) = (r : ℂ)` using `by simp [evC]`.

Simplify using `only [e, Pi.zero_apply, pow_zero, Finset.prod_const_one, div_one]`. Simplify using `using valAt_int hz r`. Consider the case `add a b _ _ ha hb`. Take `⟨δ₁, e₁, h₁, v₁, u₁⟩` from `ha`. Take `⟨δ₂, e₂, h₂, v₂, u₂⟩` from `hb`.

Use `⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁, isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm δ₁]`. Conclude with `ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)`. Rewrite using `[map_add, map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]`. Expand and normalize the polynomial expressions, which then agree.

Use `valAt_add u₁ u₂ using 1` and compare the differences between its conclusion and the goal. Establish `e : evC w (e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁) = evC w e₁ * evC w (ArakelovGeometry.xpow c δ₂) + evC w e₂ * evC w (ArakelovGeometry.xpow c δ₁)`. Simplify using `only [evC, map_add, map_mul]`. Rewrite using `[e, evC_xpow, evC_xpow, hpowC]`. Use `hW δ₁` as an intermediate fact.

Use `hW δ₂` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Consider the case `mul a b _ _ ha hb`. Take `⟨δ₁, e₁, h₁, v₁, u₁⟩` from `ha`. Take `⟨δ₂, e₂, h₂, v₂, u₂⟩` from `hb`.

Use `⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, v₁, v₂, hpow]`. Expand and normalize the polynomial expressions, which then agree. Use `CoordModel.valAt_mul u₁ u₂ using 1` and compare the differences between its conclusion and the goal. Establish `e : evC w (e₁ * e₂) = evC w e₁ * evC w e₂` using `by simp only [evC, map_mul]`.

Rewrite using `[e, hpowC]`. Use `hW δ₁` as an intermediate fact. Use `hW δ₂` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_form_valAt (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (G : MRing J), IsMultiHomog G δ ∧ aeval y G = x * ∏ k, y ⟨k, c k⟩ ^ δ k ∧
      ValAt ξ z x (evC w G / ∏ k, w ⟨k, c k⟩ ^ δ k) := by
  classical
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hW : ∀ δ : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 := fun δ =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc0 k)
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpowC : ∀ δ₁ δ₂ : K → ℕ, ∏ k, w ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, w ⟨k, c k⟩ ^ δ₁ k) * ∏ k, w ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, MvPolynomial.X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_, ?_⟩
    · rw [aeval_X, Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
      simp [div_mul_cancel₀ _ (hy k)]
    · obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
      have e1 : (∏ k', w ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k') = w ⟨k, c k⟩ := by
        rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
        simp
      have e2 : evC w (MvPolynomial.X ⟨k, i⟩ : MRing J) = w ⟨k, i⟩ := by simp [evC]
      rw [e1, e2, e, mul_div_cancel_right₀ _ (hc0 k)]
      exact hr
  | algebraMap r =>
    refine ⟨0, C r, isMultiHomog_C r, by simp, ?_⟩
    have e : evC w (C r : MRing J) = (r : ℂ) := by simp [evC]
    simp only [e, Pi.zero_apply, pow_zero, Finset.prod_const_one, div_one]
    simpa using valAt_int hz r
  | add a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁,
      isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_, ?_⟩
    · rw [add_comm δ₁]
      exact ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]
      ring
    · convert valAt_add u₁ u₂ using 1
      have e : evC w (e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁) =
          evC w e₁ * evC w (ArakelovGeometry.xpow c δ₂) + evC w e₂ * evC w (ArakelovGeometry.xpow c δ₁) := by
        simp only [evC, map_add, map_mul]
      rw [e, evC_xpow, evC_xpow, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp
  | mul a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_, ?_⟩
    · rw [map_mul, v₁, v₂, hpow]
      ring
    · convert CoordModel.valAt_mul u₁ u₂ using 1
      have e : evC w (e₁ * e₂) = evC w e₁ * evC w e₂ := by simp only [evC, map_mul]
      rw [e, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp

end Values

/- English proof (translation)
Introduce `X Ω _ ξ K _ J _ y F' _ _ ψ σ z w hN ht hw hp hz a`. Use `choose c hc using hw.1`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hw.2 k (c k) (hc k)).1`. Establish `hO : OverInt y ψ` using `overInt_of_normalCpt ht hN ψ`. Establish `hint : ∀ b : 𝓞 F', ValAt ξ z (ψ (b : F')) (σ (b : F'))`.

Introduce `b`. Take `⟨δ, G, hG, hv, hu⟩` from `exists_form_valAt hz hw c hy hc (hO.2 c hy b)`. Establish `h1` using `hp.2 (b : F') δ G (ArakelovGeometry.xpow c δ) hG (ArakelovGeometry.isMultiHomog_xpow c δ) (by`. Rewrite using `[hv, GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.aeval_xpow])`. Rewrite `h1` using `[evC_xpow]`.

Establish `hW : (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero`. Rewrite `hu` using `[h1, mul_div_cancel_right₀ _ hW]`. Then use the resulting hypothesis. Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F').2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨n, hn, hi⟩` from `halg.exists_integral_multiple`. Establish `hnC : (n : ℂ) ≠ 0` using `by exact_mod_cast hn`.

Establish `h1` using `hint (⟨n • a, hi⟩ : 𝓞 F')`. Establish `h2 : ValAt ξ z (n : Ω) ((Units.mk0 (n : ℂ) hnC : ℂˣ) : ℂ)` using `valAt_int hz n`. Take `⟨hn0, h3⟩` from `CoordModel.valAt_inv h2`. Establish `h4` using `CoordModel.valAt_mul h3 h1`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Use `show ψ a = (n : Ω)⁻¹ * ψ (n • a)`. Rewrite using `[zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ hn0]`. Use `show σ a = ((Units.mk0 (n : ℂ) hnC)⁻¹ : ℂˣ) * σ (n • a)`. Rewrite using `[zsmul_eq_mul, map_mul, map_intCast, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ hnC]`.
-/
theorem valAt_cst : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ σ z w hN ht hw hp hz a
  classical
  choose c hc using hw.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hO : OverInt y ψ := overInt_of_normalCpt ht hN ψ
  have hint : ∀ b : 𝓞 F', ValAt ξ z (ψ (b : F')) (σ (b : F')) := by
    intro b
    obtain ⟨δ, G, hG, hv, hu⟩ := exists_form_valAt hz hw c hy hc (hO.2 c hy b)
    have h1 := hp.2 (b : F') δ G (ArakelovGeometry.xpow c δ) hG (ArakelovGeometry.isMultiHomog_xpow c δ) (by
      rw [hv, GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.aeval_xpow])
    rw [evC_xpow] at h1
    have hW : (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
    rwa [h1, mul_div_cancel_right₀ _ hW] at hu
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F').2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 := hint (⟨n • a, hi⟩ : 𝓞 F')
  have h2 : ValAt ξ z (n : Ω) ((Units.mk0 (n : ℂ) hnC : ℂˣ) : ℂ) := valAt_int hz n
  obtain ⟨hn0, h3⟩ := CoordModel.valAt_inv h2
  have h4 := CoordModel.valAt_mul h3 h1
  convert h4 using 1
  · show ψ a = (n : Ω)⁻¹ * ψ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ hn0]
  · show σ a = ((Units.mk0 (n : ℂ) hnC)⁻¹ : ℂˣ) * σ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ hnC]

end GlobalTheory.CompanionTheory.Ar.Flat.LiesOver
