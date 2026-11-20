import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Use `Cm.mixed_ext fun w => ?_` and prove the remaining obligations. Establish `h : (Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z)).2 w = GlobalTheory.CuspRep.atEmb τ z w.1` using `Cm.mixRing_snd _ w`. Rewrite using `[h, PositivityTheory.Rg.Cz.GK.atEmb_apply]`. Simplify using `only [UpperTheory.ConvolutionTheory.along]`. Distinguish the cases in `e : w.1 = InfinitePlace.mk τ`.

Rewrite using `[if_pos e, if_pos e, e]`. Rewrite using `[if_neg e, if_neg e]`.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.jGen_along {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z) = UpperTheory.ConvolutionTheory.along τ z := by
  refine Cm.mixed_ext fun w => ?_
  have h : (Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z)).2 w = GlobalTheory.CuspRep.atEmb τ z w.1 := Cm.mixRing_snd _ w
  rw [h, PositivityTheory.Rg.Cz.GK.atEmb_apply]
  simp only [UpperTheory.ConvolutionTheory.along]
  by_cases e : w.1 = InfinitePlace.mk τ
  · rw [if_pos e, if_pos e, e]
  · rw [if_neg e, if_neg e]

/- English proof (translation)
Rewrite using `[Cm.ιC_apply, UpperTheory.ConvolutionTheory.elem]`. Use `congr 2`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Cm.matEq E n (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z)) = Matrix.single a b (UpperTheory.ConvolutionTheory.along τ z)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Rewrite using `[Cm.matEq_apply, Matrix.single_apply, Matrix.single_apply]`. Use `split_ifs`. Conclude with `UpperTheory.ConvolutionTheory.Dp.jGen_along τ z`. Conclude with `map_zero _`.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) (z : ℂ) :
    Cm.ιC E n (GlobalTheory.CuspRep.toL (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z))) = (1 : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b z := by
  rw [Cm.ιC_apply, UpperTheory.ConvolutionTheory.elem]
  congr 2
  refine Subtype.ext ?_
  change Cm.matEq E n (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z)) = Matrix.single a b (UpperTheory.ConvolutionTheory.along τ z)
  refine Matrix.ext fun i j => ?_
  rw [Cm.matEq_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs
  · exact UpperTheory.ConvolutionTheory.Dp.jGen_along τ z
  · exact map_zero _

/- English proof (translation)
Rewrite using `[Cm.genC, AlgRepEndIrreducible.eL, UpperTheory.ConvolutionTheory.Dp.jGen_lie, UpperTheory.ConvolutionTheory.Dp.jGen_lie, TensorProduct.smul_tmul', smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul']`. Simplify using `only [smul_eq_mul, mul_one, one_div]`.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.jGen_gen {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) :
    (2⁻¹ : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b 1 - (2⁻¹ * Complex.I) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b Complex.I = Cm.genC τ a b := by
  rw [Cm.genC, AlgRepEndIrreducible.eL, UpperTheory.ConvolutionTheory.Dp.jGen_lie, UpperTheory.ConvolutionTheory.Dp.jGen_lie, TensorProduct.smul_tmul', smul_sub,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one, one_div]

private noncomputable def UpperTheory.ConvolutionTheory.Dp.jGen_lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    HarishChandra.gl n →ₗ[ℂ] A where
  toFun X := ∑ c : Fin n × Fin n, X c.1 c.2 • F c.1 c.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r X := by simp [Finset.smul_sum, mul_smul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑ d : Fin n × Fin n, (HarishChandra.E c) d.1 d.2 • F d.1 d.2 = _`. Rewrite using `[Finset.sum_eq_single c]`. Simplify using `[HarishChandra.E]`. Introduce `d _ hd`. Establish `: ¬ (c.1 = d.1 ∧ c.2 = d.2)` using `fun h => hd (Prod.ext h.1.symm h.2.symm)`.

Simplify using `[HarishChandra.E, Matrix.single_apply, this]`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (c : Fin n × Fin n) : UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c) = F c.1 c.2 := by
  change ∑ d : Fin n × Fin n, (HarishChandra.E c) d.1 d.2 • F d.1 d.2 = _
  rw [Finset.sum_eq_single c]
  · simp [HarishChandra.E]
  · intro d _ hd
    have : ¬ (c.1 = d.1 ∧ c.2 = d.2) := fun h => hd (Prod.ext h.1.symm h.2.symm)
    simp [HarishChandra.E, Matrix.single_apply, this]
  · simp

/- English proof (translation)
Establish `hE : ∀ c d : Fin n × Fin n, UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅HarishChandra.E c, HarishChandra.E d⁆ = ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c), UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E d)⁆`. Introduce `c d`. Rewrite using `[LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, HarishChandra.E_mul_sub_mul, UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, hF, map_sub]`. Apply the tactic sequence `congr 1 <;> split_ifs <;> simp [UpperTheory.ConvolutionTheory.Dp.jGen_lin_E]`. Rewrite using `[HarishChandra.eq_sum_E X, HarishChandra.eq_sum_E Y]`.

Simplify using `only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]`.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : HarishChandra.gl n) :
    UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅X, Y⁆ = ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F X, UpperTheory.ConvolutionTheory.Dp.jGen_lin F Y⁆ := by
  have hE : ∀ c d : Fin n × Fin n, UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅HarishChandra.E c, HarishChandra.E d⁆ =
      ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c), UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E d)⁆ := by
    intro c d
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, HarishChandra.E_mul_sub_mul,
      UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, hF, map_sub]
    congr 1 <;> split_ifs <;> simp [UpperTheory.ConvolutionTheory.Dp.jGen_lin_E]
  rw [HarishChandra.eq_sum_E X, HarishChandra.eq_sum_E Y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

/- English proof (translation)
Set `L : HarishChandra.gl n →ₗ⁅ℂ⁆ A` to `{ UpperTheory.ConvolutionTheory.Dp.jGen_lin F with map_lie' := fun {X Y} => UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie F hF X Y }`. Use `⟨UniversalEnvelopingAlgebra.lift ℂ L, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[HarishChandra.e, UniversalEnvelopingAlgebra.lift_ι_apply]`. Conclude with `UpperTheory.ConvolutionTheory.Dp.jGen_lin_E F (a, b)`.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.jGen_ex {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : ∃ f : HarishChandra.U n →ₐ[ℂ] A, ∀ a b, f (HarishChandra.e (a, b)) = F a b := by
  let L : HarishChandra.gl n →ₗ⁅ℂ⁆ A :=
    { UpperTheory.ConvolutionTheory.Dp.jGen_lin F with map_lie' := fun {X Y} => UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie F hF X Y }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ L, fun a b => ?_⟩
  rw [HarishChandra.e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact UpperTheory.ConvolutionTheory.Dp.jGen_lin_E F (a, b)

/- English proof (translation)
Introduce `E _ _ _ n τ`. Establish `key : ∀ j : HarishChandra.U n →ₐ[ℂ] UpperTheory.ConvolutionTheory.UC E n, UpperTheory.ConvolutionTheory.IsJ (n` using `n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b := fun j => ⟨fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b), fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b).symm⟩`. Take `⟨f, hf⟩` from `UpperTheory.ConvolutionTheory.Dp.jGen_ex (Cm.genC (a := n) τ) (Cm.glRel_genC τ)`. Conclude with `⟨⟨f, (key f).2 hf⟩, key⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.jGen :
    UpperTheory.ConvolutionTheory.Dp.JGen := by
  intro E _ _ _ n τ
  have key : ∀ j : HarishChandra.U n →ₐ[ℂ] UpperTheory.ConvolutionTheory.UC E n,
      UpperTheory.ConvolutionTheory.IsJ (n := n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b := fun j =>
    ⟨fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b),
      fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b).symm⟩
  obtain ⟨f, hf⟩ := UpperTheory.ConvolutionTheory.Dp.jGen_ex (Cm.genC (a := n) τ) (Cm.glRel_genC τ)
  exact ⟨⟨f, (key f).2 hf⟩, key⟩
