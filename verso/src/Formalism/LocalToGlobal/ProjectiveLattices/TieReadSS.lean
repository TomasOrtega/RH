import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Establish `hM` using `siegelSpaceAlgebra_holds (E := E)`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem x hx => exact hx k`. Consider the case `zero => exact (hM r (X k) (la k) (la k) 0).1.1`. Consider the case `add x y _ _ hx hy => exact (hM r (X k) (la k) (la k) 0).1.2.1 _ hx _ hy`.

Consider the case `smul a x _ hx => exact (hM r (X k) (la k) (la k) 0).1.2.2 a _ hx`.
-/
theorem holSub_comp_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) (hP : P ∈ holSub X la) (k : Comp) :
    P k ∈ (X k).SS (la k) := by
  have hM := siegelSpaceAlgebra_holds (E := E)
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx k
  | zero => exact (hM r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact (hM r (X k) (la k) (la k) 0).1.2.1 _ hx _ hy
  | smul a x _ hx => exact (hM r (X k) (la k) (la k) 0).1.2.2 a _ hx

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

/- English proof (translation)
Introduce `u F k`. Unfold `rdR`. Establish `hF` using `F.2`. Simplify using `only [cutR] at hF`. Establish `h2` using `(Submodule.mem_inf.1 hF).1`.

Establish `h3` using `(mem_cusp _ _ _ _ _ _).1 h2`. Conclude with `holSub_comp_SS _ _ _ (h3.2 T.σ₀ (Core.good_σ₀ T.toCore)) k`.
-/
theorem tieRead_SS : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp),
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k) := by
  intro u F k
  unfold rdR
  have hF := F.2
  simp only [cutR] at hF
  have h2 := (Submodule.mem_inf.1 hF).1
  have h3 := (mem_cusp _ _ _ _ _ _).1 h2
  exact holSub_comp_SS _ _ _ (h3.2 T.σ₀ (Core.good_σ₀ T.toCore)) k

end Formalism.L2.Pj
