import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

/- English proof (translation)
Introduce `F _ _ C Y A M hM L k hpos hN`. Take `⟨r, hr, hu, hc, hf⟩` from `hN`. Establish `hE (x : Y.X) : ((k : ℕ) • A.D).IsEqn x (eqn A.D x ^ (k : ℕ))` using `(Base.isEqn_eqn A.D x).nsmul k`. Establish `hgk (x : Y.X) : ((eqn A.D x ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) * genAt A.D x ^ (k : ℕ) = 1`. Rewrite using `[genAt, Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]`.

Use `⟨by simp, r, ⟨LB.isLB_pull L.isLB M.j, hr, fun i x hx => ?_⟩, fun σ y y' i f e₂ hi hreg => ?_, fun v e y yt i e₂ hi => ?_⟩` and prove the remaining obligations. Use `(hE x).iff_unitAt.2 ?_` and prove the remaining obligations. Establish `h` using `hu i x hx`. Establish `e : ((show Y.Fnˣ from r i) : Y.Fn) / ((eqn A.D x ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) = genAt A.D x ^ (k : ℕ) * ((show Y.Fnˣ from r i) : Y.Fn)`. Rewrite using `[div_eq_mul_inv, mul_comm, ← eq_inv_of_mul_eq_one_right (hgk x)]`.

Rewrite using `[e]`. Conclude with `h`. Set `z : CxPts ((Cover.ofModel M hM).π ≫ Y.str) σ` to `⟨y.1, by show y.1 ≫ (𝟙 _ ≫ Y.str) = _`. Rewrite using `[Category.id_comp]`. Conclude with `y.2⟩`.

Establish `H` using `hc σ z y y' i (Category.comp_id _).symm e₂ hi`. Use `set g := genAt A.D (under y) with hg`. Use `set u : Y.Fn := g ^ (k : ℕ) * ((show Y.Fnˣ from r i) : Y.Fn) with hu'`. Establish `hU : UnitAt (under y) u` using `hu i (under y) hi`. Express the relevant statement in the definitionally equal form `(k : ℕ) * lnAdl A σ y = Real.log ‖ratVal u z‖ - (L.φ _).φ (i PUnit.unit) y' / 2 at H`.

Rewrite `H` using `[show ratVal u z = ratVal u y from rfl]`. Establish `hP` using `hpos σ y`. Use `set P := C.pn Y σ A.D (A.m σ) (C.cx Y σ g) y with hPdef`. Establish `hl : lnAdl A σ y = Real.log P / 2 - (A.n : ℕ) * A.ci (InfinitePlace.mk σ)` using `rfl`. Use `set a : Y.Fn := f * ((eqn A.D (under y) ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) with ha'`.

Establish `ha : RegAt (under y) a` using `(hE _).regularAt_iff.1 hreg`. Establish `hfa : f = a * g ^ (k : ℕ)`. Rewrite using `[ha', mul_assoc, hgk, mul_one]`. Establish `hgreg : ((k : ℕ) • A.D).RegularAt (under y) (g ^ (k : ℕ))`. Use `CartierDiv.isEqn_iff_generatesAt_inv.1 (hE (under y))` as an intermediate fact.

Rewrite `this` using `[Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val]`. Conclude with `this.regularAt`. Establish `e1 : C.pn Y σ ((k : ℕ) • A.D) (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y = ‖ratVal a y‖ ^ 2 * P ^ (k : ℕ)`. Rewrite using `[hfa, C.pn_mul Y σ _ _ a _ y ha hgreg, C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)]`. Establish `e2 : ratVal (f * ((show Y.Fnˣ from r i) : Y.Fn)) y = ratVal a y * ratVal u y`.

Rewrite using `[← ratVal_mul ha hU.regAt, hfa, hu', mul_assoc]`. Establish `hu0 : 0 < ‖ratVal u y‖` using `norm_pos_iff.2 (ratVal_ne_zero hU)`. Establish `key : ‖ratVal u y‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y') = P ^ (k : ℕ) * Real.exp (-(2 * ((k : ℕ) : ℝ) * (((A.n : ℕ) : ℝ) * A.ci (InfinitePlace.mk σ))))`. Establish `h1 : ‖ratVal u y‖ ^ 2 = Real.exp (Real.log (‖ratVal u y‖ ^ 2))` using `(Real.exp_log (pow_pos hu0 2)).symm`. Establish `h2 : P ^ (k : ℕ) = Real.exp (Real.log (P ^ (k : ℕ)))` using `(Real.exp_log (pow_pos hP _)).symm`.

Rewrite using `[h1, h2, ← Real.exp_add, ← Real.exp_add, Real.log_pow, Real.log_pow]`. Use `congr 1`. Rewrite `H` using `[hl]`. Use `push_cast`. Take the linear combination `(-2 : ℝ) * H`.

Express the relevant statement in the definitionally equal form `Real.exp _ * _ = ‖ratVal (f * ((show Y.Fnˣ from r i) : Y.Fn)) y‖ ^ 2 * _`. Rewrite using `[e1, e2, norm_mul, mul_pow, mul_assoc (‖ratVal a y‖ ^ 2), key]`. Put the polynomial expressions in normal form. Establish `h` using `hf v e y y.1 yt i (Category.comp_id _) e₂ hi`. Rewrite using `[Pi.zero_apply, mul_zero, sub_zero]`.

Conclude with `h`.
-/
theorem induced_of_norms : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) (L : HermLB M.p) (k : ℕ+), (∀ σ z, PosAt (A.m σ) z) → Norms (Cover.ofModel M hM) L (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => (k : ℕ) * lnAdl A σ y) (fun v e y => (k : ℕ) * A.lg v e y) → A.Induced M L k 0 := by
  intro F _ _ C Y A M hM L k hpos hN
  obtain ⟨r, hr, hu, hc, hf⟩ := hN
  have hE (x : Y.X) : ((k : ℕ) • A.D).IsEqn x (eqn A.D x ^ (k : ℕ)) := (Base.isEqn_eqn A.D x).nsmul k
  have hgk (x : Y.X) : ((eqn A.D x ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) * genAt A.D x ^ (k : ℕ) = 1 := by
    rw [genAt, Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
  refine ⟨by simp, r, ⟨LB.isLB_pull L.isLB M.j, hr, fun i x hx => ?_⟩, fun σ y y' i f e₂ hi hreg => ?_,
    fun v e y yt i e₂ hi => ?_⟩
  · refine (hE x).iff_unitAt.2 ?_
    have h := hu i x hx
    have e : ((show Y.Fnˣ from r i) : Y.Fn) / ((eqn A.D x ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) = genAt A.D x ^ (k : ℕ) * ((show Y.Fnˣ from r i) : Y.Fn) := by
      rw [div_eq_mul_inv, mul_comm, ← eq_inv_of_mul_eq_one_right (hgk x)]
    rw [e]
    exact h
  · let z : CxPts ((Cover.ofModel M hM).π ≫ Y.str) σ := ⟨y.1, by
      show y.1 ≫ (𝟙 _ ≫ Y.str) = _
      rw [Category.id_comp]
      exact y.2⟩
    have H := hc σ z y y' i (Category.comp_id _).symm e₂ hi
    set g := genAt A.D (under y) with hg
    set u : Y.Fn := g ^ (k : ℕ) * ((show Y.Fnˣ from r i) : Y.Fn) with hu'
    have hU : UnitAt (under y) u := hu i (under y) hi
    change (k : ℕ) * lnAdl A σ y = Real.log ‖ratVal u z‖ - (L.φ _).φ (i PUnit.unit) y' / 2 at H
    rw [show ratVal u z = ratVal u y from rfl] at H
    have hP := hpos σ y
    set P := C.pn Y σ A.D (A.m σ) (C.cx Y σ g) y with hPdef
    have hl : lnAdl A σ y = Real.log P / 2 - (A.n : ℕ) * A.ci (InfinitePlace.mk σ) := rfl
    set a : Y.Fn := f * ((eqn A.D (under y) ^ (k : ℕ) : Y.Fnˣ) : Y.Fn) with ha'
    have ha : RegAt (under y) a := (hE _).regularAt_iff.1 hreg
    have hfa : f = a * g ^ (k : ℕ) := by
      rw [ha', mul_assoc, hgk, mul_one]
    have hgreg : ((k : ℕ) • A.D).RegularAt (under y) (g ^ (k : ℕ)) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hE (under y))
      rw [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this
      exact this.regularAt
    have e1 : C.pn Y σ ((k : ℕ) • A.D) (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y = ‖ratVal a y‖ ^ 2 * P ^ (k : ℕ) := by
      rw [hfa, C.pn_mul Y σ _ _ a _ y ha hgreg, C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)]
    have e2 : ratVal (f * ((show Y.Fnˣ from r i) : Y.Fn)) y = ratVal a y * ratVal u y := by
      rw [← ratVal_mul ha hU.regAt, hfa, hu', mul_assoc]
    have hu0 : 0 < ‖ratVal u y‖ := norm_pos_iff.2 (ratVal_ne_zero hU)
    have key : ‖ratVal u y‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y') =
        P ^ (k : ℕ) * Real.exp (-(2 * ((k : ℕ) : ℝ) * (((A.n : ℕ) : ℝ) * A.ci (InfinitePlace.mk σ)))) := by
      have h1 : ‖ratVal u y‖ ^ 2 = Real.exp (Real.log (‖ratVal u y‖ ^ 2)) := (Real.exp_log (pow_pos hu0 2)).symm
      have h2 : P ^ (k : ℕ) = Real.exp (Real.log (P ^ (k : ℕ))) := (Real.exp_log (pow_pos hP _)).symm
      rw [h1, h2, ← Real.exp_add, ← Real.exp_add, Real.log_pow, Real.log_pow]
      congr 1
      rw [hl] at H
      push_cast
      linear_combination (-2 : ℝ) * H
    change Real.exp _ * _ = ‖ratVal (f * ((show Y.Fnˣ from r i) : Y.Fn)) y‖ ^ 2 * _
    rw [e1, e2, norm_mul, mul_pow, mul_assoc (‖ratVal a y‖ ^ 2), key]
    ring_nf
  · have h := hf v e y y.1 yt i (Category.comp_id _) e₂ hi
    rw [Pi.zero_apply, mul_zero, sub_zero]
    exact h

end GlobalTheory.CoverNorm
