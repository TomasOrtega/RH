import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.NeedPf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.RowSurjZ
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.InjectiveSequenceLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cov_aff {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (U : Pb.Cov q)
    (n : ℕ) (i : Fin (n + 1) → U.ι) : IsAffineOpen (⨅ a, U.U (i a)) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = ⨅ a, U.U (i a) := by
    refine le_antisymm (le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))) ?_
    refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le (fun a => U.U (i a)) a
  rw [e] at h
  exact h

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem cls_eq {X : TopCat.{0}} {P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X} {n : ℕ} {σ σ' : GroundTheory.Arith.SchemeCoh.Cochain P U n} (e : σ = σ')
    (h : GroundTheory.Arith.SchemeCoh.d P U n σ = 0) (h' : GroundTheory.Arith.SchemeCoh.d P U n σ' = 0) :
    GroundTheory.Arith.SchemeCoh.cls σ h = GroundTheory.Arith.SchemeCoh.cls σ' h' := by
  subst e
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem capO_pre {X Y : Scheme.{0}} (u : X ⟶ Y) {ι κ : Type} (U : ι → X.Opens) (W : κ → Y.Opens) (τ : ι → κ)
    (hτ : ∀ α, U α ≤ u ⁻¹ᵁ W (τ α)) {n : ℕ} (i : Fin n → ι) : Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO W (τ ∘ i) := by
  intro x hx
  rw [← SetLike.mem_coe, Pb.capO, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hx
  change u.base x ∈ Pb.capO W (τ ∘ i)
  rw [← SetLike.mem_coe, Pb.capO, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact fun k => hτ (i k) (hx k)

def covX {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q] : Pb.Cov q :=
  Classical.choice ((Pb.cov_ex q).1 inferInstance)

end CrystallineSemistableComparison.Om.Nt2
