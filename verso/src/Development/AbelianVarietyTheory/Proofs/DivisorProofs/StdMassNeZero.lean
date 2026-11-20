import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

/- English proof (translation)
Introduce `D N`. Use `haveI := (GlobalTheory.NormSum.cls_finite_card_le D N).1`. Use `haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))`. Establish `hne : (Finset.univ : Finset (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))).Nonempty` using `⟨DoubleCoset.mk _ _ 1, Finset.mem_univ _⟩`. Establish `hpos : (0 : ℝ) < ∑ x : GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N), ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D N) x.out : ℝ))⁻¹` using `Finset.sum_pos (fun x _ => inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D N _ le_rfl x.out).1))) hne`.

Unfold `mass`. Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `h` using `Complex.ofReal_ne_zero.2 hpos.ne'`. Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem std_mass_ne_zero : ∀ (D : D7) (N : ℕ), mass D N ≠ 0 := by
  intro D N
  haveI := (GlobalTheory.NormSum.cls_finite_card_le D N).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))
  have hne : (Finset.univ : Finset (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))).Nonempty :=
    ⟨DoubleCoset.mk _ _ 1, Finset.mem_univ _⟩
  have hpos : (0 : ℝ) < ∑ x : GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D N) x.out : ℝ))⁻¹ :=
    Finset.sum_pos (fun x _ => inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero
      (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D N _ le_rfl x.out).1))) hne
  unfold mass
  rw [finsum_eq_sum_of_fintype]
  have h := Complex.ofReal_ne_zero.2 hpos.ne'
  push_cast at h
  exact h

end GlobalTheory.NormRatio
