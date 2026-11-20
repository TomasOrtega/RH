import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

namespace GlobalTheory.Published

/- English proof (translation)
Introduce `hE hC k _ X _ p D hX L a t ha`. Establish `h` using `GlobalTheory.TwistTop.isSelfInter_shift hE hC k X p D hX L a (fun _ => t) (fun _ => rfl) ha`. Rewrite `h` using `[← mul_finsum, ← mul_assoc]`. Conclude with `h`.
-/
theorem arShift_of_arChange : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  intro hE hC k _ X _ p D hX L a t ha
  have h := GlobalTheory.TwistTop.isSelfInter_shift hE hC k X p D hX L a (fun _ => t) (fun _ => rfl) ha
  rw [← mul_finsum, ← mul_assoc] at h
  exact h

end GlobalTheory.Published
