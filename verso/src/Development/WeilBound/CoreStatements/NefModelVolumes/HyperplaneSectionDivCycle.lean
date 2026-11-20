import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

open MvPolynomial

namespace ChowFormCompatibility

/- English proof (translation)
Use extensionality with `Q`. Rewrite using `[GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply]`. Distinguish the cases in `hQ : Q ∈ GroundTheory.Heights₂.Heights.relComps J`. Use `haveI hp : Q.IsPrime := hQ.1.1.1`. Establish `h1` using `GlobalTheory.ChowHt.cast_projCycle_apply (J := J) (Q := Q) hQ`.

Rewrite using `[if_pos hQ, GroundTheory.Heights₂.Heights.localMult, dif_pos hp]`. Establish `h2` using `congrArg ENat.toNat h1`. Rewrite `h2` using `[ENat.toNat_coe]`. Conclude with `h2`. Rewrite using `[if_neg hQ]`.

Conclude with `GlobalTheory.ChowHt.projCycle_apply_of_notMem hQ`.
-/
theorem projCycle_eq_fundCycle {k : Type} [Field k] {N : ℕ} (J : Ideal (MvPolynomial (Fin N) k)) :
    GlobalTheory.ChowHt.projCycle J = GroundTheory.Heights₂.Heights.fundCycle J := by
  ext Q
  rw [GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply]
  by_cases hQ : Q ∈ GroundTheory.Heights₂.Heights.relComps J
  · haveI hp : Q.IsPrime := hQ.1.1.1
    have h1 := GlobalTheory.ChowHt.cast_projCycle_apply (J := J) (Q := Q) hQ
    rw [if_pos hQ, GroundTheory.Heights₂.Heights.localMult, dif_pos hp]
    have h2 := congrArg ENat.toNat h1
    rw [ENat.toNat_coe] at h2
    exact h2
  · rw [if_neg hQ]
    exact GlobalTheory.ChowHt.projCycle_apply_of_notMem hQ

/- English proof (translation)
Introduce `k _ N B P u f`. Use `⟨projCycle_eq_fundCycle _, ?_⟩` and prove the remaining obligations. Establish `h : (fun p : Fin (B + 1) × Fin N => (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) : Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) = GroundTheory.Heights₂.Heights.specFirstVar u`. Use function extensionality and compare the values at `⟨b, j⟩`. Proceed by induction on `b using Fin.cases with`.

Consider the case `zero => rfl`. Consider the case `succ b => rfl`. Rewrite using `[GlobalTheory.ChowHt.fixFirstBlock, h]`. Both sides reduce to the same expression.
-/
theorem hyperplane_section_divCycle : ∀ (k : Type) [Field k] (N B : ℕ) (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k), GlobalTheory.ChowHt.hyperplaneSection P u = GroundTheory.Heights₂.Heights.divCycle P u ∧ GlobalTheory.ChowHt.fixFirstBlock u f = GroundTheory.Heights₂.Heights.specFirst f u := by
  intro k _ N B P u f
  refine ⟨projCycle_eq_fundCycle _, ?_⟩
  have h : (fun p : Fin (B + 1) × Fin N =>
      (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
        Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) =
      GroundTheory.Heights₂.Heights.specFirstVar u := by
    funext ⟨b, j⟩
    induction b using Fin.cases with
    | zero => rfl
    | succ b => rfl
  rw [GlobalTheory.ChowHt.fixFirstBlock, h]
  rfl

end ChowFormCompatibility
