import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

namespace GlobalTheory.CompanionTheory.HeckeSum

/- English proof (translation)
Introduce `G V _ _ _ ρ K J _ c f hf v`. Establish `hs : ∀ j, (Function.support fun q : G ⧸ K => f j q.out • ρ q.out v).Finite`. Introduce `j`. Use `(hf j).subset ?_` and prove the remaining obligations. Introduce `q hq h0`.

Apply `hq` to reduce the goal to its premises. Use `show f j q.out • ρ q.out v = 0`. Establish `h0' : f j q.out = 0` using `h0`. Rewrite using `[h0', zero_smul]`. Establish `hs' : ∀ j ∈ (Finset.univ : Finset J), (Function.support fun q : G ⧸ K => c j • (f j q.out • ρ q.out v)).Finite`.

Introduce `j _`. Use `(hs j).subset ?_` and prove the remaining obligations. Introduce `q hq h0`. Apply `hq` to reduce the goal to its premises. Use `show c j • (f j q.out • ρ q.out v) = 0`.

Establish `h0' : f j q.out • ρ q.out v = 0` using `h0`. Rewrite using `[h0', smul_zero]`. Combine the equalities or inequalities in the displayed calculation. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_smul _ _ _`. Use `_ = ∑ j, ∑ᶠ q : G ⧸ K, c j • (f j q.out • ρ q.out v) := finsum_sum_comm _ _ hs'`. Use `_ = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_finsum' (c j) (hs j)]`.
-/
theorem finsum_coset_smul_linear :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (J : Type) [Fintype J] (c : J → ℂ) (f : J → G → ℂ),
      (∀ j, (Function.support fun q : G ⧸ K => f j q.out).Finite) → ∀ v : V,
      ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
        = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
  intro G V _ _ _ ρ K J _ c f hf v
  have hs : ∀ j, (Function.support fun q : G ⧸ K => f j q.out • ρ q.out v).Finite := by
    intro j
    refine (hf j).subset ?_
    intro q hq h0
    apply hq
    show f j q.out • ρ q.out v = 0
    have h0' : f j q.out = 0 := h0
    rw [h0', zero_smul]
  have hs' : ∀ j ∈ (Finset.univ : Finset J),
      (Function.support fun q : G ⧸ K => c j • (f j q.out • ρ q.out v)).Finite := by
    intro j _
    refine (hs j).subset ?_
    intro q hq h0
    apply hq
    show c j • (f j q.out • ρ q.out v) = 0
    have h0' : f j q.out • ρ q.out v = 0 := h0
    rw [h0', smul_zero]
  calc ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
      = ∑ᶠ q : G ⧸ K, ∑ j, c j • (f j q.out • ρ q.out v) := by
        refine finsum_congr fun q => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = ∑ j, ∑ᶠ q : G ⧸ K, c j • (f j q.out • ρ q.out v) :=
        finsum_sum_comm _ _ hs'
    _ = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_finsum' (c j) (hs j)]

end GlobalTheory.CompanionTheory.HeckeSum
