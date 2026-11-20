import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2

variable {D : D7} {C : Host.CharFrame D} {nch : NChoice D}

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [qPl, Set.mem_setOf_eq, Host.TupTied.tup]`. Use `and_congr_right fun hv => exists_congr fun w => and_congr_right fun hw => not_congr ?_` and prove the remaining obligations. Establish `hm : (C.mu0 j).UnrAt w`. Use `(C.isMu0 j).unr w fun k hk => hv ?_` and prove the remaining obligations.

Simplify using `only [gPl, Set.mem_setOf_eq]`. Conclude with `⟨w, hw, k, hk⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Establish `hx'` using `h x hx`.

Rewrite `hx'` using `[Host.HChar.loc_mul, hm x hx, one_mul]`. Conclude with `hx'`. Introduce `h x hx`. Rewrite using `[Host.HChar.loc_mul, hm x hx, h x hx, one_mul]`.
-/
theorem qPl_tup (Tp : Host.TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    qPl D (Tp.tup μ j) = {v | v ∉ gPl D ∧ ∃ w : PlE D.host, NG.OverPl w v ∧ ¬ (Tp.xi μ).UnrAt w} := by
  ext v
  simp only [qPl, Set.mem_setOf_eq, Host.TupTied.tup]
  refine and_congr_right fun hv => exists_congr fun w => and_congr_right fun hw => not_congr ?_
  have hm : (C.mu0 j).UnrAt w := by
    refine (C.isMu0 j).unr w fun k hk => hv ?_
    simp only [gPl, Set.mem_setOf_eq]
    exact ⟨w, hw, k, hk⟩
  constructor
  · intro h x hx
    have hx' := h x hx
    rw [Host.HChar.loc_mul, hm x hx, one_mul] at hx'
    exact hx'
  · intro h x hx
    rw [Host.HChar.loc_mul, hm x hx, h x hx, one_mul]

end Formalism.L2
