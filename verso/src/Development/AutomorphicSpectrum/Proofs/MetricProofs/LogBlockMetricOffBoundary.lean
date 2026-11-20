import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Take `⟨-, -, -, h1, hm⟩` from `ValRing.regAt_valAt_ring K ι Ω x z hz`. Establish `h` using `(hm s s⁻¹ hs hs').2.2.1`. Rewrite `h` using `[mul_inv_cancel₀ h0, h1]`. Establish `hne : valAt x s z ≠ 0` using `left_ne_zero_of_mul_eq_one h.symm`. Conclude with `⟨eq_inv_of_mul_eq_one_right h.symm, hne⟩`.
-/
theorem valAt_inv {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hs' : RegAt x (mCoordIdeal z) s⁻¹) :
    valAt x s⁻¹ z = (valAt x s z)⁻¹ ∧ valAt x s z ≠ 0 := by
  obtain ⟨-, -, -, h1, hm⟩ := ValRing.regAt_valAt_ring K ι Ω x z hz
  have h := (hm s s⁻¹ hs hs').2.2.1
  rw [mul_inv_cancel₀ h0, h1] at h
  have hne : valAt x s z ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact ⟨eq_inv_of_mul_eq_one_right h.symm, hne⟩

/- English proof (translation)
Introduce `h0` and use `h (by show mConeMap z (X q) = 0 rw [mConeMap, aeval_X, h0, map_zero, zero_mul])`.
-/
theorem coord_ne_zero {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 :=
  fun h0 => h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

end Values

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM p l x₀ z hp hx hz hso`. Establish `hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift x₀ x₀))` using `BM.good l x₀ hx.1`. Establish `hxb : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x)` using `BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)`. Take `⟨c, hc, hzc⟩` from `id hso`. Establish `hI : mCoordIdeal (basePart M.blk z) = mCoordIdeal (BM.Rb.lift x₀ x₀)`.

Rewrite using `[hzc]`. Conclude with `TorusAct.mCoordIdeal_torus c hc _`. Establish `hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)`. Rewrite using `[hzc]`. Conclude with `((TorusAct.main _ _ _ M.x _ c hc).2 hxb).1`.

Establish `hgood' : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z))` using `by rw [hI]; exact hgood`. Establish `hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0` using `fun k => coord_ne_zero (hgood'.1 k)`. Set `t : K → ℂ` to `fun k => if h : ∀ p', M.blk p' ≠ some k then (basePart M.blk z ⟨⟨k, h⟩, (BM.F l).c ⟨k, h⟩⟩)⁻¹ else 1`. Establish `htb : ∀ k : NonPluckerBlocks M.blk, t k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹` using `fun k => dif_pos k.2`. Establish `ht1 : ∀ k, ¬ (∀ p', M.blk p' ≠ some k) → t k = 1` using `fun k h => dif_neg h`.

Establish `ht : ∀ k, t k ≠ 0` using `fun k => by`. Distinguish the cases in `h : ∀ p', M.blk p' ≠ some k`. Rewrite using `[htb ⟨k, h⟩]`. Conclude with `inv_ne_zero (hne _)`. Rewrite using `[ht1 k h]`.

Conclude with `one_ne_zero`. Set `z₁ : (Σ k, ι k) → ℂ` to `fun q => t q.1 * z q`. Establish `hz₁ : z₁ ∈ mcPts (mCoordIdeal y)` using `((TorusAct.main _ _ _ y z t ht).2 hz).1`. Establish `hb₁ : basePart M.blk z₁ = fun q : Σ k, baseIdx ι M.blk k => t q.1.1 * basePart M.blk z q` using `rfl`. Establish `hval : valAt M.x ((BM.F l).υ p) (basePart M.blk z₁) = valAt M.x ((BM.F l).υ p) (basePart M.blk z)`.

Rewrite using `[hb₁]`. Conclude with `((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => t k.1) fun k => ht _).2 hzb).2 _`. Establish `hso₁ : SameOrbit (basePart M.blk z₁) (BM.Rb.lift x₀ x₀)` using `⟨fun k => t k.1 * c k, fun k => mul_ne_zero (ht _) (hc k), by`. Rewrite using `[hb₁, hzc]`. Use function extensionality and compare the values at `q`.

Conclude with `(mul_assoc _ _ _).symm⟩`. Establish `hnorm : ∀ k, basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = 1` using `fun k => by`. Rewrite using `[hb₁]`. Use `show t k.1 * _ = 1`. Rewrite using `[htb k]`.

Conclude with `inv_mul_cancel₀ (hne k)`. Establish `hind` using `(BM.induced l x₀ hx p z₁ hz₁ hso₁ hnorm 1 isBlockDiag_one (by simp)).2 hp`. Rewrite `hind` using `[hval]`. Establish `hscale : (BM.hom p).h z₁ = (∏ k, ‖t k‖ ^ M.dy p k) * (BM.hom p).h z`. Use `(BM.hom p).smul t z ht` as an intermediate fact.

Rewrite `this` using `[BM.hom_deg]`. Conclude with `this`. Establish `hprod : (∏ k, ‖t k‖ ^ M.dy p k) = ‖baseMono M (BM.F l) p z‖⁻¹`. Establish `e` using `Fintype.prod_subtype_mul_prod_subtype (fun k : K => ∀ p', M.blk p' ≠ some k) (fun k : K => (‖t k‖ ^ M.dy p k : ℝ))`. Rewrite using `[← e, Fintype.prod_eq_one (f := fun k : {k // ¬ ∀ p', M.blk p' ≠ some k} => ‖t k.1‖ ^ M.dy p k.1) (fun k => by rw [ht1 _ k.2]; simp), mul_one, baseMono, norm_prod, ← Finset.prod_inv_distrib]`.

Use `Finset.prod_congr (by ext; simp) fun k _ => ?_` and prove the remaining obligations. Use `show ‖t k.1‖ ^ M.dy p k.1 = (‖basePart M.blk z ⟨k, (BM.F l).c k⟩ ^ M.dy p k.1‖)⁻¹`. Rewrite using `[htb k, norm_inv, norm_zpow, _root_.inv_zpow]`. Take `⟨hu0, hu1, hu2⟩` from `hgood'.2.2 p hp`. Take `⟨hinv, hv0⟩` from `valAt_inv hzb hu0 hu1 hu2`.

Establish `hmono : baseMono M (BM.F l) p z ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)`. Establish `hpos : 0 < (BM.hom p).h z` using `(BM.hom p).pos z hz.1`. Rewrite `hind` using `[hscale, hprod, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hmono)) hpos.ne', Real.log_inv]`. Rewrite using `[hinv, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hmono) (inv_ne_zero (norm_ne_zero_iff.2 hv0)), Real.log_inv]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p l x₀ z hp hx hz hso
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift x₀ x₀)) := BM.good l x₀ hx.1
  have hxb : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  obtain ⟨c, hc, hzc⟩ := id hso

  have hI : mCoordIdeal (basePart M.blk z) = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
    rw [hzc]; exact TorusAct.mCoordIdeal_torus c hc _
  have hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [hzc]
    exact ((TorusAct.main _ _ _ M.x _ c hc).2 hxb).1
  have hgood' : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z)) := by rw [hI]; exact hgood
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k => coord_ne_zero (hgood'.1 k)

  let t : K → ℂ := fun k => if h : ∀ p', M.blk p' ≠ some k then (basePart M.blk z ⟨⟨k, h⟩, (BM.F l).c ⟨k, h⟩⟩)⁻¹ else 1
  have htb : ∀ k : NonPluckerBlocks M.blk, t k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have ht1 : ∀ k, ¬ (∀ p', M.blk p' ≠ some k) → t k = 1 := fun k h => dif_neg h
  have ht : ∀ k, t k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [htb ⟨k, h⟩]; exact inv_ne_zero (hne _)
    · rw [ht1 k h]; exact one_ne_zero
  let z₁ : (Σ k, ι k) → ℂ := fun q => t q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((TorusAct.main _ _ _ y z t ht).2 hz).1
  have hb₁ : basePart M.blk z₁ = fun q : Σ k, baseIdx ι M.blk k => t q.1.1 * basePart M.blk z q := rfl
  have hval : valAt M.x ((BM.F l).υ p) (basePart M.blk z₁) = valAt M.x ((BM.F l).υ p) (basePart M.blk z) := by
    rw [hb₁]
    exact ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => t k.1) fun k => ht _).2 hzb).2 _
  have hso₁ : SameOrbit (basePart M.blk z₁) (BM.Rb.lift x₀ x₀) :=
    ⟨fun k => t k.1 * c k, fun k => mul_ne_zero (ht _) (hc k), by
      rw [hb₁, hzc]; funext q; exact (mul_assoc _ _ _).symm⟩
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hb₁]
    show t k.1 * _ = 1
    rw [htb k]
    exact inv_mul_cancel₀ (hne k)
  have hind := (BM.induced l x₀ hx p z₁ hz₁ hso₁ hnorm 1 isBlockDiag_one (by simp)).2 hp
  rw [hval] at hind

  have hscale : (BM.hom p).h z₁ = (∏ k, ‖t k‖ ^ M.dy p k) * (BM.hom p).h z := by
    have := (BM.hom p).smul t z ht
    rw [BM.hom_deg] at this
    exact this
  have hprod : (∏ k, ‖t k‖ ^ M.dy p k) = ‖baseMono M (BM.F l) p z‖⁻¹ := by
    have e := Fintype.prod_subtype_mul_prod_subtype (fun k : K => ∀ p', M.blk p' ≠ some k)
      (fun k : K => (‖t k‖ ^ M.dy p k : ℝ))
    rw [← e, Fintype.prod_eq_one (f := fun k : {k // ¬ ∀ p', M.blk p' ≠ some k} => ‖t k.1‖ ^ M.dy p k.1)
      (fun k => by rw [ht1 _ k.2]; simp), mul_one, baseMono, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by ext; simp) fun k _ => ?_
    show ‖t k.1‖ ^ M.dy p k.1 = (‖basePart M.blk z ⟨k, (BM.F l).c k⟩ ^ M.dy p k.1‖)⁻¹
    rw [htb k, norm_inv, norm_zpow, _root_.inv_zpow]

  obtain ⟨hu0, hu1, hu2⟩ := hgood'.2.2 p hp
  obtain ⟨hinv, hv0⟩ := valAt_inv hzb hu0 hu1 hu2
  have hmono : baseMono M (BM.F l) p z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hpos : 0 < (BM.hom p).h z := (BM.hom p).pos z hz.1
  rw [hscale, hprod, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hmono)) hpos.ne', Real.log_inv] at hind
  rw [hinv, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hmono) (inv_ne_zero (norm_ne_zero_iff.2 hv0)),
    Real.log_inv]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine
