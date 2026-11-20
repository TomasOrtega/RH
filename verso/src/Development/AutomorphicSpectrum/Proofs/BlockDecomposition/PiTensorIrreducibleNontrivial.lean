import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.TensorIrr

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Conclude with `bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.ext (Subsingleton.elim _ _))`.
-/
theorem nontrivial_space_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Subsingleton.elim _ _))

/- English proof (translation)
Establish `hv : ∀ i, ∃ v : V i, v ≠ 0` using `fun i => exists_ne 0`. Use `choose v hv using hv`. Establish `hf : ∀ i, ∃ f : Module.Dual ℂ (V i), f (v i) ≠ 0` using `fun i => by`. Assume the negation of the conclusion as `hc`. Conclude with `hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 fun f => not_not.1 (not_exists.1 hc f))`.

Use `choose f hf using hf`. Set `F : MultilinearMap ℂ V ℂ` to `(MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f`. Establish `hF : PiTensorProduct.lift F (PiTensorProduct.tprod ℂ v) ≠ 0`. Rewrite using `[PiTensorProduct.lift.tprod]`. Simplify `Finset.prod_ne_zero_iff.2 fun i _ => hf i` using `[F]`.

Use `⟨PiTensorProduct.tprod ℂ v, 0, fun h => hF ?_⟩` and prove the remaining obligations. Rewrite using `[h, map_zero]`.
-/
theorem nontrivial_piTensorProduct_of_nontrivial {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  have hv : ∀ i, ∃ v : V i, v ≠ 0 := fun i => exists_ne 0
  choose v hv using hv
  have hf : ∀ i, ∃ f : Module.Dual ℂ (V i), f (v i) ≠ 0 := fun i => by
    by_contra hc
    exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1
      fun f => not_not.1 (not_exists.1 hc f))
  choose f hf using hf
  let F : MultilinearMap ℂ V ℂ := (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f
  have hF : PiTensorProduct.lift F (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [PiTensorProduct.lift.tprod]
    simpa [F] using Finset.prod_ne_zero_iff.2 fun i _ => hf i
  refine ⟨PiTensorProduct.tprod ℂ v, 0, fun h => hF ?_⟩
  rw [h, map_zero]

/- English proof (translation)
Introduce `k _ _ _ _ h x`. Establish `: ∀ a, Nontrivial (x a).2.rep.V` using `fun a => nontrivial_space_of_isIrreducible _ (x a).2.rep.irr`. Conclude with `nontrivial_piTensorProduct_of_nontrivial`.
-/
theorem nontrivial_piTensorProduct_irrGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL k), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  intro k _ _ _ _ h x
  have : ∀ a, Nontrivial (x a).2.rep.V := fun a =>
    nontrivial_space_of_isIrreducible _ (x a).2.rep.irr
  exact nontrivial_piTensorProduct_of_nontrivial

end GlobalTheory.CompanionTheory.TensorIrr
