import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

/- English proof (translation)
Rewrite using `[liftM, dif_pos h]`.
-/
theorem liftM_coe_of_mem (M : IntermediateField ℚ ℂ) {x : ℂ} (h : x ∈ M) : ((liftM M x : M) : ℂ) = x := by
  rw [liftM, dif_pos h]

/- English proof (translation)
Use `letI : Algebra K ℂ := φ₀.toAlgebra`. Use `haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E`. Set `f : ι → (E →ₐ[K] ℂ)` to `fun i => { emb i with commutes' := fun y => hres i y }`. Establish `hfinj : Function.Injective f` using `fun i j h => hinj (RingHom.ext fun x => AlgHom.congr_fun h x)`. Establish `hbij : Function.Bijective f` using `(Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [hcard, AlgHom.card K E ℂ]⟩`.

Establish `htr` using `trace_eq_sum_embeddings ℂ (K := K) (L := E) (x := a)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_emb_eq_trace_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (a : E) :
    ∑ i, emb i a = φ₀ (Algebra.trace K E a) := by
  letI : Algebra K ℂ := φ₀.toAlgebra
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  let f : ι → (E →ₐ[K] ℂ) := fun i => { emb i with commutes' := fun y => hres i y }
  have hfinj : Function.Injective f := fun i j h => hinj (RingHom.ext fun x => AlgHom.congr_fun h x)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [hcard, AlgHom.card K E ℂ]⟩
  have htr := trace_eq_sum_embeddings ℂ (K := K) (L := E) (x := a)
  calc ∑ i, emb i a = ∑ i, f i a := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ a := hbij.sum_comp (fun σ => σ a)
    _ = φ₀ (Algebra.trace K E a) := htr.symm

/- English proof (translation)
Establish `hsum` using `sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard a`. Establish `hmem : φ₀ (Algebra.trace K E a) ∈ M` using `hsum ▸ M.sum_mem (fun i _ => hM i a)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[IntermediateField.coe_sum, liftM_coe_of_mem M hmem, ← hsum]`. Conclude with `Finset.sum_congr rfl fun i _ => liftM_coe_of_mem M (hM i a)`.
-/
theorem sum_emb_eq_trace (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (a : E) :
    ∑ i, liftM M (emb i a) = liftM M (φ₀ (Algebra.trace K E a)) := by
  have hsum := sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard a
  have hmem : φ₀ (Algebra.trace K E a) ∈ M := hsum ▸ M.sum_mem (fun i _ => hM i a)
  apply Subtype.ext
  rw [IntermediateField.coe_sum, liftM_coe_of_mem M hmem, ← hsum]
  exact Finset.sum_congr rfl fun i _ => liftM_coe_of_mem M (hM i a)

/- English proof (translation)
Establish `hexp : ∀ x, emb k x = ∑ i', emb i' x * ∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j)`. Introduce `x`. Use `conv_lhs => rw [← ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e).sum_repr x]`. Rewrite using `[map_sum]`. Simplify using `only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul, hres, ← sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hLI : LinearIndependent ℂ (fun i => ((emb i : E →+* ℂ) : E → ℂ))` using `(linearIndependent_monoidHom E ℂ).comp (fun i => (emb i).toMonoidHom) (fun i j h => hinj (RingHom.ext fun x => DFunLike.congr_fun h x))`. Rewrite `hLI` using `[Fintype.linearIndependent_iff]`. Establish `h` using `hLI (fun i' => (∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j)) - if i' = k then 1 else 0) (by`.

Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[sub_eq_zero, hexp x]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _) i`. Rewrite `h` using `[sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem sum_emb_dualBasis_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, emb i (e j) * emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j) =
      if i = k then 1 else 0 := by
  have hexp : ∀ x, emb k x = ∑ i', emb i' x * ∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j) := by
    intro x
    conv_lhs => rw [← ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e).sum_repr x]
    rw [map_sum]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      hres, ← sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => by ring
  have hLI : LinearIndependent ℂ (fun i => ((emb i : E →+* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun i => (emb i).toMonoidHom)
      (fun i j h => hinj (RingHom.ext fun x => DFunLike.congr_fun h x))
  rw [Fintype.linearIndependent_iff] at hLI
  have h := hLI (fun i' => (∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j)) - if i' = k then 1 else 0) (by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, hexp x]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _) i
  rwa [sub_eq_zero] at h

/- English proof (translation)
Establish `hc` using `sum_emb_dualBasis_complex K E φ₀ ι emb hinj hres hcard e i k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[IntermediateField.coe_sum]`. Simplify using `only [IntermediateField.coe_mul, liftM_coe_of_mem M (hM _ _)]`. Rewrite using `[hc]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sum_emb_dualBasis (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, liftM M (emb i (e j)) *
        liftM M (emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j)) =
      if i = k then 1 else 0 := by
  have hc := sum_emb_dualBasis_complex K E φ₀ ι emb hinj hres hcard e i k
  apply Subtype.ext
  rw [IntermediateField.coe_sum]
  simp only [IntermediateField.coe_mul, liftM_coe_of_mem M (hM _ _)]
  rw [hc]
  split_ifs <;> simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
