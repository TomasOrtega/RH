import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullbackStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

/- English proof (translation)
Establish `hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source)` using `x.ch.isOpen_inter_preimage_symm x'.ch.open_source`. Establish `hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source` using `⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩`. Use `Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_` and prove the remaining obligations. Use `show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))`. Set `p : A.Pt` to `⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩`.

Set `p' : A.Pt` to `⟨(x'.1.1, x.ch.symm y), hy.2⟩`. Establish `e1 : A.loc α x.1.1 y = α p` using `by rw [HolAtlas.loc, dif_pos hy.1]`. Establish `e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p'` using `A.loc_crd α p'`. Establish `e3 : p.crd = y` using `x.ch.right_inv hy.1`. Rewrite using `[e1, e2, hα.compat p p' rfl]`.

Use `show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _`. Rewrite using `[e3]`.
-/
theorem loc_eventuallyEq_pull {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun y => pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y)) := by
  have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  refine Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_
  show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))
  let p : A.Pt := ⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩
  let p' : A.Pt := ⟨(x'.1.1, x.ch.symm y), hy.2⟩
  have e1 : A.loc α x.1.1 y = α p := by rw [HolAtlas.loc, dif_pos hy.1]
  have e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p' := A.loc_crd α p'
  have e3 : p.crd = y := x.ch.right_inv hy.1
  rw [e1, e2, hα.compat p p' rfl]
  show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _
  rw [e3]

/- English proof (translation)
Assemble the required witnesses or components as `⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source, ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩, A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩`.
-/
theorem chg_facts (x x' : A.Pt) (h : x.pt = x'.pt) :
    IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧ x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source ∧
    DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧
    (x'.ch ∘ x.ch.symm) x.crd = x'.crd :=
  ⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source,
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩,
    A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩

/- English proof (translation)
The claim follows from `((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)`.
-/
theorem loc_diffAt {α : A.Fld} (hα : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x.1.1 y) S) x.crd :=
  ((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)

/- English proof (translation)
Establish `hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target → A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v`. Introduce `T i v hv`. Rewrite using `[HolAtlas.loc, dif_pos hv]`. Use `show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _`. Rewrite using `[(A.e i).right_inv hv]`.

Use `⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩` and prove the remaining obligations. Conclude with `((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by`. Rewrite using `[show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]`. Take `⟨hU, hxU, hτ, hτx⟩` from `chg_facts A x x' h`. Establish `hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd)`.

Rewrite using `[hτx]`. Conclude with `loc_diffAt A hα x'`. Use `show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)`. Rewrite using `[((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1, (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]`. Conclude with `((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by`.

Rewrite using `[show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]`. Take `⟨hU, hxU, hτ, hτx⟩` from `chg_facts A x x' h`. Establish `hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd)`. Rewrite using `[hτx]`. Conclude with `loc_diffAt A hα x'`.

Use `show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)`. Rewrite using `[((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2, (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]`.
-/
theorem isForm_del_dbar {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  have hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target →
      A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v := by
    intro T i v hv
    rw [HolAtlas.loc, dif_pos hv]
    show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by
      rw [show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by
      rw [show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]

end GlobalTheory.CxForm.HolAtlas

/- English proof (translation)
Introduce `_ _ _ A _ hα` and use `A.isForm_del_dbar hα`.
-/
theorem GlobalTheory.CxForm.isForm_del_dbar : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) :=
  fun _ _ _ A _ hα => A.isForm_del_dbar hα
