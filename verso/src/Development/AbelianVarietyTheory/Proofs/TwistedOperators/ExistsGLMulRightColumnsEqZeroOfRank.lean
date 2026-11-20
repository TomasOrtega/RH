import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

/- English proof (translation)
Set `f` to `x.mulVecLin`. Take `⟨C, hKC⟩` from `Submodule.exists_isCompl (LinearMap.ker f)`. Establish `hcard : Fintype.card n = Fintype.card a + Fintype.card b`. Rewrite using `[← Fintype.card_congr e, Fintype.card_sum]`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker f`.

Establish `hrank : Module.finrank k (LinearMap.range f) = Fintype.card a` using `hx`. Rewrite `hrn` using `[hrank, Module.finrank_fintype_fun_eq_card, hcard]`. Establish `hK : Module.finrank k (LinearMap.ker f) = Fintype.card b` using `by omega`. Establish `hsum` using `Submodule.finrank_add_eq_of_isCompl hKC`. Rewrite `hsum` using `[hK, Module.finrank_fintype_fun_eq_card, hcard]`.

Establish `hC : Module.finrank k C = Fintype.card a` using `by omega`. Set `bK : Module.Basis b k (LinearMap.ker f)` to `(Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm`. Set `bC : Module.Basis a k C` to `(Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm`. Set `B : Module.Basis n k (n → k)` to `((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e`. Establish `hB : ∀ j, f (B (e (Sum.inr j))) = 0`.

Introduce `j`. Simplify using `[B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]`. Set `P` to `(Pi.basisFun k n).toMatrix B`. Establish `: Invertible P` using `(Pi.basisFun k n).invertibleToMatrix B`. Use `⟨unitOfInvertible P, fun i j => ?_⟩` and prove the remaining obligations.

Use `show (x * P) i (e (Sum.inr j)) = 0`. Establish `hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i`. Simplify using `[P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]`. Rewrite using `[hcol, hB j]`. Both sides reduce to the same expression.
-/
theorem exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl

end GlobalTheory
