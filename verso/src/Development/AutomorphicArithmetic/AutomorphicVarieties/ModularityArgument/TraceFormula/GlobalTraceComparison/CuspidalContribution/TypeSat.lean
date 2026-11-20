import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

/- English proof (translation)
Introduce `G _ W hW`. Set `W0 : Submodule ℂ (G → ℂ)` to `{ carrier := {f | ∀ a, (fun k => f (a * k)) ∈ W} add_mem' := fun {f g} hf hg a => W.add_mem (hf a) (hg a) zero_mem' := fun _ => W.zero_mem smul_mem' := fun c f hf a => W.smul_mem c (hf a) }`. Establish `hle : W0 ≤ W`. Introduce `f hf`. Establish `h1 : (fun k => f (1 * k)) ∈ W` using `hf 1`.

Simplify using `using h1`. Use `haveI : FiniteDimensional ℂ W0 := Submodule.finiteDimensional_of_le hle`. Establish `hstab : ∀ (a : G) (f : G → ℂ), f ∈ W0 → (fun k => f (a * k)) ∈ W0`. Introduce `a f hf c`. Establish `h1 : (fun k => f ((a * c) * k)) ∈ W` using `hf (a * c)`.

Simplify `h1` using `[mul_assoc]`. Set `L : G → (W0 →ₗ[ℂ] W0)` to `fun a => { toFun := fun f => ⟨fun k => f.1 (a * k), hstab a f.1 f.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `b` to `Module.finBasis ℂ W0`. Set `c : (Fin (Module.finrank ℂ W0) × Fin (Module.finrank ℂ W0)) → G → ℂ` to `fun p k => b.repr (L k (b p.2)) p.1`. Use `⟨Submodule.span ℂ (Set.range c), FiniteDimensional.span_of_finite ℂ (Set.finite_range c), ?_⟩` and prove the remaining obligations.

Introduce `f hf y`. Set `F : W0` to `⟨f, hf⟩`. Establish `key : (fun k => f (k * y)) = ∑ i, ∑ j, ((b i).1 y * b.repr F j) • c (i, j)`. Use function extensionality and compare the values at `k`. Establish `h3 : L k F = ∑ j, b.repr F j • L k (b j)` using `by conv_lhs => rw [← b.sum_repr F]`.

Simplify using `only [map_sum, map_smul]`. Establish `h4 : ∀ i, b.repr (L k F) i = ∑ j, b.repr F j * c (i, j) k`. Introduce `i`. Rewrite using `[h3]`. Simplify using `[c, Finsupp.finset_sum_apply]`.

Establish `h5 : f (k * y) = (L k F).1 y` using `rfl`. Establish `h6 : (L k F).1 y = ∑ i, b.repr (L k F) i * (b i).1 y`. Establish `h7` using `congrArg (fun v : W0 => (v : G → ℂ) y) (b.sum_repr (L k F))`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h7`. Conclude with `h7.symm`.

Rewrite using `[h5, h6]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h4, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.typeSat :
    TypeSat := by
  intro G _ W hW
  let W0 : Submodule ℂ (G → ℂ) :=
    { carrier := {f | ∀ a, (fun k => f (a * k)) ∈ W}
      add_mem' := fun {f g} hf hg a => W.add_mem (hf a) (hg a)
      zero_mem' := fun _ => W.zero_mem
      smul_mem' := fun c f hf a => W.smul_mem c (hf a) }
  have hle : W0 ≤ W := by
    intro f hf
    have h1 : (fun k => f (1 * k)) ∈ W := hf 1
    simpa using h1
  haveI : FiniteDimensional ℂ W0 := Submodule.finiteDimensional_of_le hle
  have hstab : ∀ (a : G) (f : G → ℂ), f ∈ W0 → (fun k => f (a * k)) ∈ W0 := by
    intro a f hf c
    have h1 : (fun k => f ((a * c) * k)) ∈ W := hf (a * c)
    simpa [mul_assoc] using h1
  let L : G → (W0 →ₗ[ℂ] W0) := fun a =>
    { toFun := fun f => ⟨fun k => f.1 (a * k), hstab a f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b := Module.finBasis ℂ W0
  let c : (Fin (Module.finrank ℂ W0) × Fin (Module.finrank ℂ W0)) → G → ℂ :=
    fun p k => b.repr (L k (b p.2)) p.1
  refine ⟨Submodule.span ℂ (Set.range c),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c), ?_⟩
  intro f hf y
  let F : W0 := ⟨f, hf⟩
  have key : (fun k => f (k * y)) =
      ∑ i, ∑ j, ((b i).1 y * b.repr F j) • c (i, j) := by
    funext k
    have h3 : L k F = ∑ j, b.repr F j • L k (b j) := by
      conv_lhs => rw [← b.sum_repr F]
      simp only [map_sum, map_smul]
    have h4 : ∀ i, b.repr (L k F) i = ∑ j, b.repr F j * c (i, j) k := by
      intro i
      rw [h3]
      simp [c, Finsupp.finset_sum_apply]
    have h5 : f (k * y) = (L k F).1 y := rfl
    have h6 : (L k F).1 y = ∑ i, b.repr (L k F) i * (b i).1 y := by
      have h7 := congrArg (fun v : W0 => (v : G → ℂ) y) (b.sum_repr (L k F))
      simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul] at h7
      exact h7.symm
    rw [h5, h6]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h4, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
