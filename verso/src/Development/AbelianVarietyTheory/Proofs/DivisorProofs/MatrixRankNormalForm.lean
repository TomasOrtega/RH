import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ A D _ _ _ _ X`. Set `V` to `LinearMap.range X.mulVecLin`. Set `b : Module.Basis (Fin X.rank) K V` to `Module.finBasis K V`. Take `⟨g, hg⟩` from `LinearMap.exists_extend (p := V) b.equivFun.toLinearMap`. Establish `hpre : ∀ i, ∃ v : D → K, X *ᵥ v = ((b i : V) : A → K)` using `fun i => by`.

Take `⟨v, hv⟩` from `LinearMap.mem_range.mp (b i).2`. Conclude with `⟨v, hv⟩`. Use `choose q hq using hpre`. Use `⟨LinearMap.toMatrix' g, Matrix.of fun d i => q i d, ?_⟩` and prove the remaining obligations. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises.

Introduce `j`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.one_mulVec]`. Establish `hcol : (Matrix.of fun d i => q i d).col j = q j`. Use extensionality with `d`. Simplify using `[Matrix.col]`.

Rewrite using `[hcol, hq j, LinearMap.toMatrix'_mulVec]`. Use `congrArg (fun f => f (b j)) hg` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at this`. Rewrite using `[this]`. Use extensionality with `k`.

Rewrite using `[Module.Basis.equivFun_self]`. Simplify using `[Pi.single_apply, Finsupp.single_apply, eq_comm]`.
-/
theorem rank_frame_exists :
    ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K),
        H * X * Q = 1 := by
  intro K _ A D _ _ _ _ X
  classical
  let V := LinearMap.range X.mulVecLin
  let b : Module.Basis (Fin X.rank) K V := Module.finBasis K V
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V) b.equivFun.toLinearMap
  have hpre : ∀ i, ∃ v : D → K, X *ᵥ v = ((b i : V) : A → K) := fun i => by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (b i).2
    exact ⟨v, hv⟩
  choose q hq using hpre
  refine ⟨LinearMap.toMatrix' g, Matrix.of fun d i => q i d, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
    Matrix.one_mulVec]
  have hcol : (Matrix.of fun d i => q i d).col j = q j := by
    ext d; simp [Matrix.col]
  rw [hcol, hq j, LinearMap.toMatrix'_mulVec]
  have := congrArg (fun f => f (b j)) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe] at this
  rw [this]
  ext k
  rw [Module.Basis.equivFun_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

end GlobalTheory
