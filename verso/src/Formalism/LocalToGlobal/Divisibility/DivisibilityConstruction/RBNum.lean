import Formalism.LocalToGlobal.Divisibility.RecBridge

open Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV

variable {D : D7}

/- English proof (translation)
The claim follows from `ofRecord_rd D L Del h0`.
-/
theorem rdTie (L : SizeData₂ D) (Del h0 : ℕ) : (ofRecord D L Del h0).rd = D.host.rdE := ofRecord_rd D L Del h0

/- English proof (translation)
Simplify using `only [NumDatum.mainT, SizeData₂.MAIN]`. Rewrite using `[← Finset.sum_coe_sort D.host.TT]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[ofRecord_aT, ofRecord_logOm]`. Use `first`.

Consider the case `rfl`. Consider the case `(unfold Formalism.LatticeIndexTer.ph phF; ring)`.
-/
theorem mainTie (L : SizeData₂ D) (Del h0 : ℕ) (u : D.what₂.Word) :
    (ofRecord D L Del h0).mainT (D.mem u).A.T = L.MAIN u := by
  simp only [NumDatum.mainT, SizeData₂.MAIN]
  rw [← Finset.sum_coe_sort D.host.TT]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ofRecord_aT, ofRecord_logOm]
  first
  | rfl
  | (unfold Formalism.LatticeIndexTer.ph phF; ring)

/- English proof (translation)
The claim follows from `numRecTie_ofRecord L Del h0 u (rdTie L Del h0) (mainTie L Del h0 u)`.
-/
theorem numRecTie_record (L : SizeData₂ D) (Del h0 : ℕ) (u : D.what₂.Word) :
    NumRecTie (ofRecord D L Del h0) L u ((D.mem u).A.T) L.Nc :=
  numRecTie_ofRecord L Del h0 u (rdTie L Del h0) (mainTie L Del h0 u)

end Formalism.L2.DIV.Cons

end
