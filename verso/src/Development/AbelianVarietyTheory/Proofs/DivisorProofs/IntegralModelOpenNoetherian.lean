import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.ModelNoeth

/- English proof (translation)
Distinguish the cases in `h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ V.nonunits`. Take `⟨n, hn, hV⟩` from `h`. Use `(GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hn hV).1` as an intermediate fact. Use `infer_instance`. Use `push_neg at h`.

Establish `hall : ∀ x : L, x ∈ V`. Introduce `x`. Use `IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)` as an intermediate fact. Use `Algebra.IsAlgebraic.trans ℤ ℚ L` as an intermediate fact. Take `⟨y, hy0, hy⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple`.

Establish `hyx : y • x ∈ V`. Establish `h' : IsIntegral V (y • x)` using `hy.tower_top`. Take `⟨z, hz⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp h'`. Conclude with `hz ▸ z.2`. Establish `hn : (y.natAbs : L) ∉ V.nonunits` using `h _ (by simpa using hy0)`.

Rewrite `hn` using `[ValuationSubring.mem_nonunits_iff, not_lt]`. Establish `hn1 : V.valuation (y.natAbs : L) = 1` using `le_antisymm (by simpa using V.valuation_le_one (y.natAbs : V)) hn`. Establish `hy1 : V.valuation (y : L) = 1`. Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite using `[e]`.

Simplify using `using hn1`. Rewrite using `[e]`. Simplify using `using hn1`. Rewrite `hyx`, the goal using `[← V.valuation_le_one_iff]`. Rewrite `hyx` using `[zsmul_eq_mul, map_mul, hy1, _root_.one_mul]`.

Conclude with `hyx`. Establish `hF : IsField V`. Use `⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩` and prove the remaining obligations. Use `⟨⟨(a : L)⁻¹, hall _⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `: (a : L) ≠ 0` using `fun e => ha (Subtype.ext e)`.

Simplify using `[this]`. Use `letI := hF.toField`. Use `infer_instance`.
-/
theorem isNoetherianRing_valuationSubring {L : Type} [Field L] [NumberField L] (V : ValuationSubring L) :
    IsNoetherianRing V := by
  by_cases h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ V.nonunits
  · obtain ⟨n, hn, hV⟩ := h
    have := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hn hV).1
    infer_instance
  · push_neg at h
    have hall : ∀ x : L, x ∈ V := by
      intro x
      have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
      have := Algebra.IsAlgebraic.trans ℤ ℚ L
      obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple
      have hyx : y • x ∈ V := by
        have h' : IsIntegral V (y • x) := hy.tower_top
        obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp h'
        exact hz ▸ z.2
      have hn : (y.natAbs : L) ∉ V.nonunits := h _ (by simpa using hy0)
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
      have hn1 : V.valuation (y.natAbs : L) = 1 :=
        le_antisymm (by simpa using V.valuation_le_one (y.natAbs : V)) hn
      have hy1 : V.valuation (y : L) = 1 := by
        rcases Int.natAbs_eq y with e | e
        · rw [e]; simpa using hn1
        · rw [e]; simpa using hn1
      rw [← V.valuation_le_one_iff] at hyx ⊢
      rw [zsmul_eq_mul, map_mul, hy1, _root_.one_mul] at hyx
      exact hyx
    have hF : IsField V := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
      refine ⟨⟨(a : L)⁻¹, hall _⟩, Subtype.ext ?_⟩
      have : (a : L) ≠ 0 := fun e => ha (Subtype.ext e)
      simp [this]
    letI := hF.toField
    infer_instance

end GlobalTheory.ModelNoeth

open GlobalTheory.ModelNoeth in
/- English proof (translation)
Introduce `E _ _ _ H Dw l' Xo' c' W Y A _ ξ hξ`. Use `c'.fin` as an intermediate fact. Establish `: NumberField c'.F` using `{}`. Establish `: IsNoetherianRing (c'.V W)` using `isNoetherianRing_valuationSubring _`. Take `⟨N, i, hi, hs⟩` from `Y.proj`.

Establish `: IsProper (PSpace.str (c'.V W) N)` using `isProper_str _ _`. Establish `: LocallyOfFiniteType (i ≫ PSpace.str (c'.V W) N)` using `inferInstance`. Establish `: IsLocallyNoetherian Y.X` using `LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (c'.V W) N)`. Conclude with `isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion ξ)`.
-/
theorem GlobalTheory.ModelNoeth.isNoetherianRing_of_isOpenImmersion :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X), IsOpenImmersion ξ → IsNoetherianRing A := by
  intro E _ _ _ H Dw l' Xo' c' W Y A _ ξ hξ
  have := c'.fin
  have : NumberField c'.F := {}
  have : IsNoetherianRing (c'.V W) := isNoetherianRing_valuationSubring _
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  have : IsProper (PSpace.str (c'.V W) N) := isProper_str _ _
  have : LocallyOfFiniteType (i ≫ PSpace.str (c'.V W) N) := inferInstance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (c'.V W) N)
  exact isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion ξ)
