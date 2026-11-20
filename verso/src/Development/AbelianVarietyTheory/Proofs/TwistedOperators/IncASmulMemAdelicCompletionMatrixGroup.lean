import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.HatScalar

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨v, hv, u, hu, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.vecMulVec_smul]`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `neg_mem hx`.
-/
theorem smul_mem_tens_of {E : Type} [Field E] [NumberField E] {n r : ℕ} {Λ : Lt E n} {L L' : Lt E r} (c : E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) :
    c • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, y, hy, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨α, hα, c • y, smul_mem_tens_of c h hy, ?_⟩` and prove the remaining obligations.

Use extensionality with `a k`. Simplify using `only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Use `show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E) c * _ = _`. Rewrite using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem incA_smul_mem_hatA (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank)
    (c : D.host.E) (h : ∀ v ∈ L1, c • v ∈ L2) :
    ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, c • y, smul_mem_tens_of c h hy, ?_⟩
    ext a k
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E) c *
      _ = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.HatScalar
