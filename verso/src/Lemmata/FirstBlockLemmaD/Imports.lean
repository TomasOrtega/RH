import Mathlib

namespace Bl.FirstBlockLemmaD

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] (x y : PadicAlgCl p),
  LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) (Max.max.{0} (Norm.norm.{0} x) (Norm.norm.{0} y)) := by
  intro p inst x y
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rw [norm_neg, ← sub_eq_add_neg] at h
  exact h

end Bl.FirstBlockLemmaD
