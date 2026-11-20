import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

/- English proof (translation)
Unfold `holSub at hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem Q hQ`. Conclude with `holCusp_mem_holSub X la fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 (w k) (Q k) (hQ k)`. Consider the case `zero`.

Establish `: (fun k x => w k * (0 : FDSec X) k x) = (0 : FDSec X)`. Use function extensionality and compare the values at `k x`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add Q R _ _ hQ hR`. Establish `: (fun k x => w k * (Q + R) k x) = ((fun k x => w k * Q k x) + (fun k x => w k * R k x) : FDSec X)`. Use function extensionality and compare the values at `k x`. Simplify using `[mul_add]`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hQ hR`. Consider the case `smul a Q _ hQ`. Establish `: (fun k x => w k * (a • Q) k x) = (a • (fun k x => w k * Q k x) : FDSec X)`. Use function extensionality and compare the values at `k x`. Simplify using `[mul_left_comm]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hQ`.
-/
theorem compMul_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) {P : FDSec X}
    (hP : P ∈ holSub X la) : (fun k x => w k * P k x) ∈ holSub X la := by
  unfold holSub at hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact holCusp_mem_holSub X la fun k =>
      (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 (w k) (Q k) (hQ k)
  | zero =>
    have : (fun k x => w k * (0 : FDSec X) k x) = (0 : FDSec X) := by
      funext k x; simp
    rw [this]; exact Submodule.zero_mem _
  | add Q R _ _ hQ hR =>
    have : (fun k x => w k * (Q + R) k x) =
        ((fun k x => w k * Q k x) + (fun k x => w k * R k x) : FDSec X) := by
      funext k x; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hQ hR
  | smul a Q _ hQ =>
    have : (fun k x => w k * (a • Q) k x) = (a • (fun k x => w k * Q k x) : FDSec X) := by
      funext k x; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hQ

/- English proof (translation)
Introduce `E _ _ _ r Comp X la w P`. Use `⟨compMul_mem_holSub X la w, fun h => ⟨compMul_mem_holSub X la w h.1, fun k x hx => ?_⟩⟩` and prove the remaining obligations. Establish `h0 : P k x = 0` using `h.2 k x hx`. Use `show w k * P k x = 0`. Rewrite using `[h0, mul_zero]`.
-/
theorem holSub_compMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) (P : FDSec X), (P ∈ holSub X la → (fun k x => w k * P k x) ∈ holSub X la) ∧ (P ∈ holSub0 X la → (fun k x => w k * P k x) ∈ holSub0 X la) := by
  intro E _ _ _ r Comp X la w P
  refine ⟨compMul_mem_holSub X la w, fun h => ⟨compMul_mem_holSub X la w h.1, fun k x hx => ?_⟩⟩
  have h0 : P k x = 0 := h.2 k x hx
  show w k * P k x = 0
  rw [h0, mul_zero]

end GlobalTheory.CompRat
