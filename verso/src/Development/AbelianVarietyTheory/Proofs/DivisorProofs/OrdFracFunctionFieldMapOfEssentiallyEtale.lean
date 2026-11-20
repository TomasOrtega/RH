import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

/- English proof (translation)
Introduce `M W _ _ p f _ E E' h htr het hft g`. Use `set φ := functionFieldMap f`. Use `set ρ := φ.restrict E.ring E'.ring h`. Use `letI := ρ.toAlgebra`. Use `haveI : Algebra.FormallyEtale E.ring E'.ring := het`.

Use `haveI : Algebra.EssFiniteType E.ring E'.ring := hft`. Use `haveI : IsLocalHom (algebraMap E.ring E'.ring) := by`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx.exists_right_inv`. Establish `e : φ (x : W.functionField) * (y : M.functionField) = 1` using `congrArg Subtype.val hy`.

Establish `hx0 : (x : W.functionField) ≠ 0`. Introduce and unpack `h0`. Rewrite `e` using `[h0, map_zero, zero_mul]`. Conclude with `zero_ne_one e`. Establish `hinv : φ ((x : W.functionField)⁻¹) = y`.

Rewrite using `[map_inv₀]`. Conclude with `inv_eq_of_mul_eq_one_right e`. Establish `hmem : (x : W.functionField)⁻¹ ∈ E.ring` using `htr _ (hinv ▸ y.2)`. Conclude with `IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))`. Establish `hm` using `Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)`.

Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible E.ring`. Establish `ht' : Irreducible (ρ t)`. Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Take `⟨m, u, e⟩` from `exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero`.

Establish `h1` using `ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m`. Establish `h2` using `ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m`. Rewrite `h1` using `[← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj]`. Establish `e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) = algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) * algebraMap E'.ring M.functionField (ρ t) ^ m`. Rewrite using `[Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]`.

Both sides reduce to the same expression. Rewrite `h2` using `[← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj]`. Conclude with `h2.trans h1.symm`.
-/
theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
