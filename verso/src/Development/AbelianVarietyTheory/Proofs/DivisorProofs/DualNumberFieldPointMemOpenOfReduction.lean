import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
namespace GlobalTheory.MBLow.TanGauge

/- English proof (translation)
Introduce `C _ X y U h q _`. Establish `key : ∃ p : (Sp C : Scheme.{0}), (redE C) p = q`. Establish `hsub : Subsingleton (PrimeSpectrum (DualNumber C))`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Establish `aux : ∀ a : PrimeSpectrum (DualNumber C), ∀ x, x ∈ a.asIdeal ↔ x.fst = 0`.

Introduce `a x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hne`. Conclude with `a.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))`.

Introduce `hx`. Use `a.2.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `: x ^ 2 = 0`. Apply the tactic sequence `ext <;> simp [sq, hx]`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Use extensionality with `x`. Rewrite using `[aux, aux]`. Conclude with `⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C), hsub.elim _ _⟩`. Take `⟨p, rfl⟩` from `key`.

Conclude with `h (x := p) trivial`.
-/
theorem top_le_of_redE : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  intro C _ X y U h q _
  have key : ∃ p : (Sp C : Scheme.{0}), (redE C) p = q := by
    have hsub : Subsingleton (PrimeSpectrum (DualNumber C)) := by
      refine ⟨fun a b => ?_⟩
      have aux : ∀ a : PrimeSpectrum (DualNumber C), ∀ x, x ∈ a.asIdeal ↔ x.fst = 0 := by
        intro a x
        constructor
        · intro hx
          by_contra hne
          exact a.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
        · intro hx
          refine a.2.mem_of_pow_mem 2 ?_
          have : x ^ 2 = 0 := by
            ext <;> simp [sq, hx]
          rw [this]; exact zero_mem _
      ext x; rw [aux, aux]
    exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C), hsub.elim _ _⟩
  obtain ⟨p, rfl⟩ := key
  exact h (x := p) trivial
end GlobalTheory.MBLow.TanGauge
