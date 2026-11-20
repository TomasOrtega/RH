import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ValAdd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `hf.exists_fnOf`. Take `⟨W, hW, b, rfl⟩` from `hg.exists_fnOf`. Establish `hy : y ∈ ptsIn p σ (U ⊓ W)` using `mem_ptsIn.2 ⟨hU, hW⟩`. Rewrite using `[← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)), ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add, ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]`.
-/
theorem ratVal_add' {σ : k →+* ℂ} {y : CxPts p σ} {f g : X.functionField} (hf : RegAt (under y) f)
    (hg : RegAt (under y) g) : ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

/- English proof (translation)
Establish `hi` using `mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)`. Establish `hj` using `mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)`. Establish `e : P.loc a b (f + g) (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) = P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) + P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)`. Simplify using `only [Pair.loc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[val, val, val, e, ratVal_add' (hf _ _ _ hi hj) (hg _ _ _ hi hj), add_mul]`.
-/
theorem val_add (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) {f g : X.functionField}
    (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) : val P a b σ y (f + g) = val P a b σ y f + val P a b σ y g := by
  have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
  have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
  have e : P.loc a b (f + g) (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
      P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) +
        P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]; ring
  rw [val, val, val, e, ratVal_add' (hf _ _ _ hi hj) (hg _ _ _ hi hj), add_mul]

end GlobalTheory.HSAmp.ValAdd

open GlobalTheory.HSAmp.ValAdd in

/- English proof (translation)
Introduce `k _ X _ p P a b σ y`. Use `⟨{ toFun := fun f => val P a b σ y f, map_zero' := ?_, map_add' := fun f g => val_add P a b σ y f.2 g.2 }, fun _ => rfl⟩` and prove the remaining obligations. Use `val_add P a b σ y (zero_mem (P.H a b)) (zero_mem (P.H a b))` as an intermediate fact. Simplify using `only [add_zero] at this`. Simplify using `using this`.
-/
theorem GlobalTheory.HSAmp.val_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  intro k _ X _ p P a b σ y
  refine ⟨{ toFun := fun f => val P a b σ y f, map_zero' := ?_, map_add' := fun f g => val_add P a b σ y f.2 g.2 }, fun _ => rfl⟩
  have := val_add P a b σ y (zero_mem (P.H a b)) (zero_mem (P.H a b))
  simp only [add_zero] at this
  simpa using this
