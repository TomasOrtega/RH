import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ X _ p D h`. Establish `hΓ : CharZero Γ(X, ⊤)` using `h.charZero`. Establish `hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom` using `germ_injective_of_isIntegral X _ _`. Establish `hK : CharZero X.functionField` using `(RingHom.charZero_iff hg).1 hΓ`. Use `⟨hK, ?_⟩` and prove the remaining obligations.

Use `h.isDomain` as an intermediate fact. Use `h.finite` as an intermediate fact. Establish `hint : Algebra.IsIntegral ℤ k` using `inferInstance`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `n hn`. Rewrite `hn` using `[Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero]`.

Simplify using `[hn]`. Establish `: a ∈ RingHom.ker (GlobalTheory.toFunctionField p)` using `ha`. Rewrite `this` using `[hker]`. Conclude with `this`.
-/
theorem isArithVar_charZero_functionField_and_injective :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
      IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  intro k _ X _ p D h
  have hΓ : CharZero Γ(X, ⊤) := h.charZero
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom :=
    germ_injective_of_isIntegral X _ _
  have hK : CharZero X.functionField := (RingHom.charZero_iff hg).1 hΓ
  refine ⟨hK, ?_⟩
  have := h.isDomain
  have := h.finite
  have hint : Algebra.IsIntegral ℤ k := inferInstance
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have : a ∈ RingHom.ker (GlobalTheory.toFunctionField p) := ha
  rw [hker] at this
  exact this

end GlobalTheory
