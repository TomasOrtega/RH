import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]`. Simplify using the standard rewrite rules. Consider the case `succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul]`. Conclude with `CartierDiv.eff_zero`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `ih.add h`.
-/
theorem eff_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

/- English proof (translation)
Introduce `X _ _ p hp N a b D B hD hB`. Use `letI := algebraΓOfHom p`. Take `⟨-, H, hH⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp`. Take `⟨m, D₀, hm, hD₀, rfl, hDn⟩` from `hD`. Take `⟨m', B₀, hm', hB₀, rfl, hBn⟩` from `hB`.

Use `⟨m * m', m' • D₀ + m • B₀, Nat.mul_pos hm hm', (eff_nsmul_of_qadd hD₀ m').add (eff_nsmul_of_qadd hB₀ m), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul_of_qadd]`. Establish `h1 : (m : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `h2 : (m' : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hm'.ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `C hC`. Establish `e` using `hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • D₀ + m • B₀)) (isLB_lbPow (isLB_toLB D₀) m') (isLB_lbPow (isLB_toLB B₀) m) (by rw [cls_lbPow (isLB_toLB D₀), cls_lbPow (isLB_toLB B₀), ← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul])`. Rewrite `e` using `[hC.interNumRed_lbPow hH (isLB_toLB D₀), hC.interNumRed_lbPow hH (isLB_toLB B₀)]`.

Establish `h1 : (m : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `h2 : (m' : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hm'.ne'`. Establish `hD'` using `hDn C hC`. Establish `hB'` using `hBn C hC`. Rewrite using `[e]`.

Use `push_cast`. Rewrite `hD'` using `[div_eq_iff h1]`. Rewrite `hB'` using `[div_eq_iff h2]`. Rewrite using `[div_eq_iff (mul_ne_zero h1 h2), hD', hB']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qNum_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ (N : LB X) (a b : ℚ) (D B : X → ℚ), QNum p N a D → QNum p N b B →
      QNum p N (a + b) (D + B) := by
  intro X _ _ p hp N a b D B hD hB
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m, D₀, hm, hD₀, rfl, hDn⟩ := hD
  obtain ⟨m', B₀, hm', hB₀, rfl, hBn⟩ := hB
  refine ⟨m * m', m' • D₀ + m • B₀, Nat.mul_pos hm hm', (eff_nsmul_of_qadd hD₀ m').add
    (eff_nsmul_of_qadd hB₀ m), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul_of_qadd]
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    push_cast
    field_simp
  · intro C hC
    have e := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • D₀ + m • B₀))
      (isLB_lbPow (isLB_toLB D₀) m') (isLB_lbPow (isLB_toLB B₀) m)
      (by rw [cls_lbPow (isLB_toLB D₀), cls_lbPow (isLB_toLB B₀), ← toPic_apply, ← toPic_apply,
        ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (isLB_toLB D₀), hC.interNumRed_lbPow hH (isLB_toLB B₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have hD' := hDn C hC
    have hB' := hBn C hC
    rw [e]
    push_cast
    rw [div_eq_iff h1] at hD'
    rw [div_eq_iff h2] at hB'
    rw [div_eq_iff (mul_ne_zero h1 h2), hD', hB']
    ring

end GlobalTheory.PairStep
