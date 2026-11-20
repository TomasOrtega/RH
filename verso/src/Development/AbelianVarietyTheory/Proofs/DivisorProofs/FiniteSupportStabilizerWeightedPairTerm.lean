import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer

open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

/- English proof (translation)
Introduce `Γ Y _ _ F hF hfin hS`. Use `(hS.biUnion (t := fun o' => (fun γ : Γ => (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of γ))) '' Function.support (F (Quotient.out o'))) (fun o' _ => (hfin _).image _)).subset ?_` and prove the remaining obligations. Introduce `o ho`. Establish `hne : F (Quotient.out o).1 (val (Quotient.out o).2) ≠ 0`. Introduce `h`.

Apply `ho` to reduce the goal to its premises. Simplify using `[pairTerm, h]`. Use `set p := Quotient.out o with hp`. Use `set o' : MulAction.orbitRel.Quotient Γ Y := Quotient.mk (MulAction.orbitRel Γ Y) p.1 with ho'`. Take `⟨η, hη⟩` from `Quotient.exact (Quotient.out_eq o')`.

Express the relevant statement in the definitionally equal form `η • p.1 = Quotient.out o' at hη`. Establish `hval : F (Quotient.out o') (η * val p.2 * η⁻¹) ≠ 0`. Rewrite using `[← hη, hF]`. Conclude with `hne`. Use `Set.mem_biUnion (x := o') ⟨_, hval⟩ ⟨η * val p.2 * η⁻¹, hval, ?_⟩` and prove the remaining obligations.

Establish `hsm : (η • p : Y × ConjSelf Γ) = (Quotient.out o', of (η * val p.2 * η⁻¹))`. Rewrite using `[Prod.smul_def, hη]`. Both sides reduce to the same expression. Use `show Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of (η * val p.2 * η⁻¹)) = o`. Rewrite using `[← hsm]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finite_support_pairTerm :
    ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ),
      (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) →
      (∀ y : Y, (Function.support (F y)).Finite) →
      {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite →
      (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) =>
        pairTerm F (Quotient.out o))).Finite := by
  intro Γ Y _ _ F hF hfin hS
  refine (hS.biUnion (t := fun o' =>
      (fun γ : Γ => (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of γ))) ''
        Function.support (F (Quotient.out o'))) (fun o' _ => (hfin _).image _)).subset ?_
  intro o ho
  have hne : F (Quotient.out o).1 (val (Quotient.out o).2) ≠ 0 := by
    intro h
    apply ho
    simp [pairTerm, h]
  set p := Quotient.out o with hp
  set o' : MulAction.orbitRel.Quotient Γ Y := Quotient.mk (MulAction.orbitRel Γ Y) p.1 with ho'
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq o')
  change η • p.1 = Quotient.out o' at hη
  have hval : F (Quotient.out o') (η * val p.2 * η⁻¹) ≠ 0 := by
    rw [← hη, hF]; exact hne
  refine Set.mem_biUnion (x := o') ⟨_, hval⟩ ⟨η * val p.2 * η⁻¹, hval, ?_⟩
  have hsm : (η • p : Y × ConjSelf Γ) = (Quotient.out o', of (η * val p.2 * η⁻¹)) := by
    rw [Prod.smul_def, hη]; rfl
  show Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of (η * val p.2 * η⁻¹)) = o
  rw [← hsm]
  calc Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (η • p)
      = Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p :=
        Quotient.sound ⟨η, rfl⟩
    _ = o := by rw [hp]; exact Quotient.out_eq o

end GlobalTheory.OrbitUnfold
