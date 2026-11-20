import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallDual

open GlobalTheory GlobalTheory.HTLat TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HTLat.AnnKer

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P`. Use `set L := Submodule.span C (Set.range P.bLie) with hL`. Establish `hWL : P.W = P.pairV.orthogonal L`. Use extensionality with `x`. Rewrite using `[KerPerp.mem_W_iff p C v O Λ P x, LinearMap.BilinForm.mem_orthogonal_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h n hn`. Establish `: L ≤ LinearMap.ker (P.pairV.flip x)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `h z)`.

Conclude with `this hn`. Introduce `h y`. Conclude with `h _ (Submodule.subset_span ⟨y, rfl⟩)`. Establish `hl : ∀ w : P.V, (∀ y, P.pairV w y = 0) → w = 0` using `fun w hw => P.eq_of_pairV fun t => by rw [hw, map_zero, LinearMap.zero_apply]`. Establish `hnd : P.pairV.Nondegenerate` using `⟨hl, fun w hw => hl w fun y => by rw [P.pairV_swap, hw, neg_zero]⟩`.

Establish `hrefl : P.pairV.IsRefl` using `fun x y h => by rw [P.pairV_swap, h, neg_zero]`. Use `⟨fun x => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl L, ← hWL, LinearMap.BilinForm.mem_orthogonal_iff]`. Use `⟨fun h n hn => ?_, fun h y hy => ?_⟩` and prove the remaining obligations. Conclude with `hrefl _ _ (h n hn)`.

Conclude with `hrefl _ _ (h y hy)`. Establish `ho` using `LinearMap.BilinForm.finrank_orthogonal hnd L`. Rewrite `ho` using `[← hWL, P.finrank_V]`. Establish `hle : Module.finrank C L ≤ 2 * P.A.g` using `P.finrank_V ▸ Submodule.finrank_le L`. Use linear arithmetic over natural numbers and integers.
-/
theorem annW_eq_span_bLie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), (∀ x : P.V, (∀ y ∈ P.W, P.pairV x y = 0) ↔ x ∈ Submodule.span C (Set.range P.bLie)) ∧ Module.finrank C (Submodule.span C (Set.range P.bLie)) + Module.finrank C P.W = 2 * P.A.g := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  set L := Submodule.span C (Set.range P.bLie) with hL
  have hWL : P.W = P.pairV.orthogonal L := by
    ext x
    rw [KerPerp.mem_W_iff p C v O Λ P x, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h n hn
      have : L ≤ LinearMap.ker (P.pairV.flip x) := Submodule.span_le.2 (by
        rintro _ ⟨z, rfl⟩
        exact h z)
      exact this hn
    · intro h y
      exact h _ (Submodule.subset_span ⟨y, rfl⟩)
  have hl : ∀ w : P.V, (∀ y, P.pairV w y = 0) → w = 0 := fun w hw =>
    P.eq_of_pairV fun t => by rw [hw, map_zero, LinearMap.zero_apply]
  have hnd : P.pairV.Nondegenerate :=
    ⟨hl, fun w hw => hl w fun y => by rw [P.pairV_swap, hw, neg_zero]⟩
  have hrefl : P.pairV.IsRefl := fun x y h => by rw [P.pairV_swap, h, neg_zero]
  refine ⟨fun x => ?_, ?_⟩
  · rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl L, ← hWL,
      LinearMap.BilinForm.mem_orthogonal_iff]
    refine ⟨fun h n hn => ?_, fun h y hy => ?_⟩
    · exact hrefl _ _ (h n hn)
    · exact hrefl _ _ (h y hy)
  · have ho := LinearMap.BilinForm.finrank_orthogonal hnd L
    rw [← hWL, P.finrank_V] at ho
    have hle : Module.finrank C L ≤ 2 * P.A.g := P.finrank_V ▸ Submodule.finrank_le L
    omega

end GlobalTheory.HTLat.AnnKer
