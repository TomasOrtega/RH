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
Establish `hint : (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `right`. Use `⟨⟨α, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce `v`.

Conclude with `hα v`. Establish `hgen : (fun i => Formalism.UG.inclE (F` using `D.host.F) (Af D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := Submodule.subset_span ⟨x, hx, rfl⟩`. Use `Submodule.smul_mem _ (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) hgen` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `only [one_mul, finPart, Formalism.IndefR.Lev.swapAE, Formalism.UG.inclE]`. Use `show _ = ((1 : D.host.E) ⊗ₜ[D.host.F] α) * (x i ⊗ₜ[D.host.F] (1 : Af D.host.F))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Both sides reduce to the same expression.
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
Introduce `D S L P y hy`. Set `Φ : (Fin S.rank → AE D) →+ (Fin S.rank → Formalism.IndefR.Lev.EAf D)` to `AddMonoidHom.compLeft ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)).toAddMonoidHom (Fin S.rank)`. Establish `hle : latV S L P ≤ (Formalism.L2.Herm.hatL (F` using `D.host.F) L).toAddSubgroup.comap Φ := by`. Unfold `GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨α, hα, -, a, ha, x, hx, rfl⟩`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality. Conclude with `gen_mem D S L α hα x hx`. Conclude with `hle hy`.
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
