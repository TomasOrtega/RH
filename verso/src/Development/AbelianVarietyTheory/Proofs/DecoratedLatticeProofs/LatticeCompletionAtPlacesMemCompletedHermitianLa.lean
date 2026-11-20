import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatVHat

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem gen_mem (D : D7) (S : HSp D) (L : Lat S) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (x : Fin S.rank → D.host.E)
    (hx : x ∈ L) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((1 : D.host.E) * x i)))) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) L := by
  have hint : (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    apply Subring.subset_closure
    right
    refine ⟨⟨α, ?_⟩, rfl⟩
    intro v
    exact hα v
  have hgen : (fun i => Formalism.UG.inclE (F := D.host.F) (Af D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have := Submodule.smul_mem _ (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) hgen
  convert this using 1
  funext i
  simp only [one_mul, finPart, Formalism.IndefR.Lev.swapAE, Formalism.UG.inclE]
  show _ = ((1 : D.host.E) ⊗ₜ[D.host.F] α) * (x i ⊗ₜ[D.host.F] (1 : Af D.host.F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem latV_mem_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  intro D S L P y hy
  let Φ : (Fin S.rank → AE D) →+ (Fin S.rank → Formalism.IndefR.Lev.EAf D) :=
    AddMonoidHom.compLeft ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)).toAddMonoidHom (Fin S.rank)
  have hle : latV S L P ≤ (Formalism.L2.Herm.hatL (F := D.host.F) L).toAddSubgroup.comap Φ := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact gen_mem D S L α hα x hx
  exact hle hy

end GlobalTheory.LatVHat
