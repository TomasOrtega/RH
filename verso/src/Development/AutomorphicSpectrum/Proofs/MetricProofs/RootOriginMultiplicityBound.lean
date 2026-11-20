import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or nu n₀ m hn hn₀ hn₀' hm hm'`. Use function extensionality and compare the values at `k₁`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Establish `hL : ∀ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) = -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (fundCo (nu r.1) r.2 * ∑ k ∈ Finset.Iic r.2, (RM.xdeg (r.1, k) k₁ : ℝ)))`. Introduce and unpack `⟨τ, i⟩`.

Rewrite using `[Or.fund_deg τ i]`. Use `push_cast`. Rewrite using `[hm (τ, i)]`. Simplify using `only [Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hR : ∀ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) = -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (nu r.1 r.2 * (RM.xdeg r k₁ : ℝ)))`. Introduce `r`. Establish `h1 : (RM.line 1 (some r)).a = RM.xdeg r` using `RM.x_deg 1 r`. Rewrite using `[h1, hn₀ r]`. Use `push_cast`.

Use `hn r` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) = ∑ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ)`.

Simplify using `only [hL, hR, Finset.sum_neg_distrib, ← Finset.mul_sum]`. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_prod_type]`. Use `congr 2`. Conclude with `Finset.sum_congr rfl fun τ _ => sum_fundCo_mul_sum_Iic (nu τ) fun k => (RM.xdeg (τ, k) k₁ : ℝ)`. Establish `hnone : (Or.Re.ref none).a k₁ = (RM.line 1 none).a k₁`.

Rewrite using `[Or.ref_none.1]`. Both sides reduce to the same expression. Simplify using `only [combLine, Fintype.sum_option, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hm', hn₀', hnone]`. Move the coercions through the operations in `at hsum ⊢`.

Rewrite using `[hsum]`.
-/
theorem combLine_ref_a_eq_line_a : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)) (n₀ m : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → (∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2) → m none = -(Fx.q' : ℤ) → (combLine Or.Re.ref m).a = (combLine (RM.line 1) n₀).a := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or nu n₀ m hn hn₀ hn₀' hm hm'
  funext k₁
  apply Int.cast_injective (α := ℝ)
  have hL : ∀ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (fundCo (nu r.1) r.2 * ∑ k ∈ Finset.Iic r.2, (RM.xdeg (r.1, k) k₁ : ℝ))) := by
    rintro ⟨τ, i⟩
    rw [Or.fund_deg τ i]
    push_cast
    rw [hm (τ, i)]
    simp only [Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, Nat.cast_mul]
    ring
  have hR : ∀ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (nu r.1 r.2 * (RM.xdeg r k₁ : ℝ))) := by
    intro r
    have h1 : (RM.line 1 (some r)).a = RM.xdeg r := RM.x_deg 1 r
    rw [h1, hn₀ r]
    push_cast
    have := hn r
    push_cast at this
    rw [this]
    ring
  have hsum : ∑ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      ∑ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) := by
    simp only [hL, hR, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 2
    exact Finset.sum_congr rfl fun τ _ => sum_fundCo_mul_sum_Iic (nu τ) fun k => (RM.xdeg (τ, k) k₁ : ℝ)
  have hnone : (Or.Re.ref none).a k₁ = (RM.line 1 none).a k₁ := by
    rw [Or.ref_none.1]
    rfl
  simp only [combLine, Fintype.sum_option, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hm', hn₀', hnone]
  push_cast at hsum ⊢
  rw [hsum]

end GlobalTheory.CompanionTheory.Ar.Small.Fund
