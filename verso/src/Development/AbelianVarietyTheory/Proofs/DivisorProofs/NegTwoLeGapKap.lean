import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

namespace GlobalTheory.HSApp.GapArith

/- English proof (translation)
Unfold `gap`. Use `split_ifs`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

/- English proof (translation)
Unfold `gap`. Use `split_ifs`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem gap_nsmul {N : ℕ} (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = (n : ℤ) * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]; ring
  · simp

/- English proof (translation)
Simplify using `only [gap, dif_pos h, FlagTan.kap]`. Apply the tactic sequence `split_ifs <;> push_cast <;> omega`.
-/
theorem neg_two_le_gap_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : -2 ≤ gap (FlagTan.kap Dw τ) k := by
  simp only [gap, dif_pos h, FlagTan.kap]
  split_ifs <;> push_cast <;> omega

/- English proof (translation)
Introduce `hB`. Establish `hD : 1 ≤ dimFlag Dw` using `hB.one_le`. Establish `h4 : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q → 4 ≤ gap (P.u₁ τ) k`. Introduce `τ k hk`. Establish `h` using `hB.gaps τ k hk`.

Establish `hb : 4 ≤ (dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3)` using `Nat.le_trans (by omega : 4 ≤ (dimFlag Dw + 3) * 1) (Nat.mul_le_mul_left _ (by omega))`. Establish `hb' : (4 : ℤ) ≤ (((dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) : ℕ) : ℤ)`. Conclude with `hb` after adjusting the coercions. Conclude with `hb'.trans h`. Establish `hu₂ : ∀ (τ : Psi H) (k : ℕ), gap (P.u₂ τ) k = gap (P.u₁ τ) k + gap (P.rem τ) k`.

Introduce `τ k`. Conclude with `gap_add _ _ _`. Establish `hwt : ∀ (i : ℕ) (τ : Psi H) (k : ℕ), gap (P.wt i τ) k = gap (FlagTan.kap Dw τ) k + gap (P.u₂ τ) k + (dimFlag Dw : ℤ) * gap (P.u₁ τ) k + (i : ℤ) * gap (P.u₁ τ) k`. Introduce `i τ k`. Establish `e : P.wt i τ = FlagTan.kap Dw τ + P.u₂ τ + dimFlag Dw • P.u₁ τ + i • P.u₁ τ` using `rfl`.

Rewrite using `[e, gap_add, gap_add, gap_add, gap_nsmul, gap_nsmul]`. Use `⟨fun τ k hk => by have := h4 τ k hk; omega, fun τ k hk => ?_, fun i τ k hk => ?_⟩` and prove the remaining obligations. Use `h4 τ k hk` as an intermediate fact. Use `(P.gap_rem τ k).1` as an intermediate fact. Rewrite using `[hu₂]`.

Use linear arithmetic over natural numbers and integers. Establish `a` using `h4 τ k hk`. Establish `b` using `(P.gap_rem τ k).1`. Establish `c` using `neg_two_le_gap_kap Dw τ hk`. Rewrite using `[hwt, hu₂]`.

Establish `d : (4 : ℤ) ≤ (dimFlag Dw : ℤ) * gap (P.u₁ τ) k`. Establish `: (1 : ℤ) ≤ dimFlag Dw` using `by exact_mod_cast hD`. Use the polynomial consequences of the given equalities and inequalities. Establish `e : (0 : ℤ) ≤ (i : ℤ) * gap (P.u₁ τ) k` using `by positivity`. Use linear arithmetic over natural numbers and integers.
-/
theorem gaps_main (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (P : WtPar Dw) : WtBig P → GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ i : ℕ, GapGe 1 (P.wt i) := by
  intro hB
  have hD : 1 ≤ dimFlag Dw := hB.one_le
  have h4 : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q → 4 ≤ gap (P.u₁ τ) k := by
    intro τ k hk
    have h := hB.gaps τ k hk
    have hb : 4 ≤ (dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) :=
      Nat.le_trans (by omega : 4 ≤ (dimFlag Dw + 3) * 1)
        (Nat.mul_le_mul_left _ (by omega))
    have hb' : (4 : ℤ) ≤ (((dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) : ℕ) : ℤ) := by
      exact_mod_cast hb
    exact hb'.trans h
  have hu₂ : ∀ (τ : Psi H) (k : ℕ), gap (P.u₂ τ) k = gap (P.u₁ τ) k + gap (P.rem τ) k := by
    intro τ k
    exact gap_add _ _ _
  have hwt : ∀ (i : ℕ) (τ : Psi H) (k : ℕ), gap (P.wt i τ) k =
      gap (FlagTan.kap Dw τ) k + gap (P.u₂ τ) k + (dimFlag Dw : ℤ) * gap (P.u₁ τ) k + (i : ℤ) * gap (P.u₁ τ) k := by
    intro i τ k
    have e : P.wt i τ = FlagTan.kap Dw τ + P.u₂ τ + dimFlag Dw • P.u₁ τ + i • P.u₁ τ := rfl
    rw [e, gap_add, gap_add, gap_add, gap_nsmul, gap_nsmul]
  refine ⟨fun τ k hk => by have := h4 τ k hk; omega, fun τ k hk => ?_, fun i τ k hk => ?_⟩
  · have := h4 τ k hk
    have := (P.gap_rem τ k).1
    rw [hu₂]; omega
  · have a := h4 τ k hk
    have b := (P.gap_rem τ k).1
    have c := neg_two_le_gap_kap Dw τ hk
    rw [hwt, hu₂]
    have d : (4 : ℤ) ≤ (dimFlag Dw : ℤ) * gap (P.u₁ τ) k := by
      have : (1 : ℤ) ≤ dimFlag Dw := by exact_mod_cast hD
      nlinarith
    have e : (0 : ℤ) ≤ (i : ℤ) * gap (P.u₁ τ) k := by positivity
    omega

end GlobalTheory.HSApp.GapArith
