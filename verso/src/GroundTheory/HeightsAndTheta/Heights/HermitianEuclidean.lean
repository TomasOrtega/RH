import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HermitianSum

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section RealToFibre

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

def realToComplexAt : ℝ →ₗ[ℤ] ComplexAt σ :=
  ((ofComplex σ).toRingHom.comp Complex.ofRealHom).toAddMonoidHom.toIntLinearMap

def realToFibre : ℝ ⊗[ℤ] E →ₗ[ℤ] Fibre σ E :=
  TensorProduct.lift
    (((TensorProduct.mk (𝓞 K) (ComplexAt σ) E).restrictScalars₁₂ ℤ ℤ).compl₁₂
      (realToComplexAt σ) LinearMap.id)

variable {σ E}

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realToFibre_tmul (r : ℝ) (e : E) :
    realToFibre σ E (r ⊗ₜ e) = ofComplex σ (r : ℂ) ⊗ₜ e := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [smul_zero, map_zero]`. Consider the case `tmul s e`. Rewrite using `[smul_tmul', realToFibre_tmul, realToFibre_tmul, smul_tmul', complex_smul_def, smul_eq_mul, Complex.ofReal_mul, map_mul]`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`.
-/
theorem realToFibre_smul (r : ℝ) (x : ℝ ⊗[ℤ] E) :
    realToFibre σ E (r • x) = (r : ℂ) • realToFibre σ E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s e =>
    rw [smul_tmul', realToFibre_tmul, realToFibre_tmul, smul_tmul', complex_smul_def, smul_eq_mul,
      Complex.ofReal_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul r e => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem realToFibre_lTensor {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] (φ : E →ₗ[𝓞 K] F)
    (x : ℝ ⊗[ℤ] E) :
    realToFibre σ F (LinearMap.lTensor ℝ (φ.restrictScalars ℤ) x) =
      LinearMap.lTensor (ComplexAt σ) φ (realToFibre σ E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end RealToFibre

variable [NumberField K]

/- English proof (translation)
Use `set b := RingOfIntegers.basis K`. Use `set B := Algebra.TensorProduct.basis ℝ b`. Establish `hxB : x = ∑ i, B.repr x i • B i` using `(B.sum_repr x).symm`. Establish `hli` using `(canonicalEmbedding.latticeBasis K).linearIndependent`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`.

Establish `key : ∀ i, B.repr x i = 0`. Introduce `i`. Establish `h0` using `hli (fun j ↦ (B.repr x j : ℂ)) ?_ i`. Conclude with `h0` after adjusting the coercions. Use function extensionality and compare the values at `σ`.

Establish `hσ` using `congrArg (integersCoord K σ) (hx σ)`. Rewrite `hσ` using `[hxB, map_sum, map_sum, map_zero]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, integralBasis_apply, Pi.zero_apply, smul_eq_mul]`. Rewrite using `[← hσ]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[realToFibre_smul, map_smul, Algebra.TensorProduct.basis_apply, realToFibre_tmul, integersCoord_tmul, smul_eq_mul]`. Rewrite using `[Complex.ofReal_one, map_one, map_one, mul_one]`. Rewrite using `[hxB]`. Simplify using `only [key, zero_smul, Finset.sum_const_zero]`.
-/
theorem realToFibre_integers_eq_zero (x : ℝ ⊗[ℤ] 𝓞 K)
    (hx : ∀ σ : K →+* ℂ, realToFibre σ (𝓞 K) x = 0) : x = 0 := by
  classical
  set b := RingOfIntegers.basis K
  set B := Algebra.TensorProduct.basis ℝ b
  have hxB : x = ∑ i, B.repr x i • B i := (B.sum_repr x).symm
  have hli := (canonicalEmbedding.latticeBasis K).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have key : ∀ i, B.repr x i = 0 := by
    intro i
    have h0 := hli (fun j ↦ (B.repr x j : ℂ)) ?_ i
    · exact_mod_cast h0
    funext σ
    have hσ := congrArg (integersCoord K σ) (hx σ)
    rw [hxB, map_sum, map_sum, map_zero] at hσ
    simp only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply,
      canonicalEmbedding.apply_at, integralBasis_apply, Pi.zero_apply, smul_eq_mul]
    rw [← hσ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [realToFibre_smul, map_smul, Algebra.TensorProduct.basis_apply, realToFibre_tmul,
      integersCoord_tmul, smul_eq_mul]
    rw [Complex.ofReal_one, map_one, map_one, mul_one]
  rw [hxB]
  simp only [key, zero_smul, Finset.sum_const_zero]

/- English proof (translation)
The claim follows from `Module.Finite.trans (𝓞 K) E`.
-/
theorem finite_int (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] : Module.Finite ℤ E :=
  Module.Finite.trans (𝓞 K) E

/- English proof (translation)
Establish `: Module.Finite ℤ E` using `finite_int K E`. Establish `: Module.Flat ℤ E` using `Module.Flat.trans ℤ (𝓞 K) E`. Use `infer_instance`.
-/
theorem free_int (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] : Module.Free ℤ E := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Flat ℤ E := Module.Flat.trans ℤ (𝓞 K) E
  infer_instance

section General

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

/- English proof (translation)
Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' (𝓞 K) E`. Take `⟨s, hs⟩` from `f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)`. Set `φ : Fin n → (E →ₗ[𝓞 K] 𝓞 K)` to `fun i ↦ LinearMap.proj i ∘ₗ s`. Set `g : Fin n → E` to `fun i ↦ f (fun j ↦ if i = j then 1 else 0)`. Establish `hdecomp : ∀ e : E, ∑ i, φ i e • g i = e`.

Introduce `e`. Establish `h1 : f (s e) = e` using `by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]`. Use `conv_rhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ f (s e)]`. Both sides reduce to the same expression. Establish `hdec : ∀ y : ℝ ⊗[ℤ] E, ∑ i, LinearMap.lTensor ℝ ((LinearMap.toSpanSingleton (𝓞 K) E (g i)).restrictScalars ℤ) (LinearMap.lTensor ℝ ((φ i).restrictScalars ℤ) y) = y`.

Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, Finset.sum_const_zero]`. Consider the case `tmul r e`. Simplify using `only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply]`.

Rewrite using `[← tmul_sum, hdecomp]`. Consider the case `add y z hy hz`. Simplify using `only [map_add, Finset.sum_add_distrib]`. Rewrite using `[hy, hz]`. Establish `hφ : ∀ i, LinearMap.lTensor ℝ ((φ i).restrictScalars ℤ) x = 0`.

Introduce `i`. Use `realToFibre_integers_eq_zero _ fun σ ↦ ?_` and prove the remaining obligations. Rewrite using `[realToFibre_lTensor, hx σ, map_zero]`. Rewrite using `[← hdec x]`. Simplify using `only [hφ, map_zero, Finset.sum_const_zero]`.
-/
theorem realToFibre_eq_zero (x : ℝ ⊗[ℤ] E) (hx : ∀ σ : K →+* ℂ, realToFibre σ E x = 0) :
    x = 0 := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) E
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let φ : Fin n → (E →ₗ[𝓞 K] 𝓞 K) := fun i ↦ LinearMap.proj i ∘ₗ s
  let g : Fin n → E := fun i ↦ f (fun j ↦ if i = j then 1 else 0)
  have hdecomp : ∀ e : E, ∑ i, φ i e • g i = e := by
    intro e
    have h1 : f (s e) = e := by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
    conv_rhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ f (s e)]
    rfl
  have hdec : ∀ y : ℝ ⊗[ℤ] E, ∑ i, LinearMap.lTensor ℝ
      ((LinearMap.toSpanSingleton (𝓞 K) E (g i)).restrictScalars ℤ)
      (LinearMap.lTensor ℝ ((φ i).restrictScalars ℤ) y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, Finset.sum_const_zero]
    | tmul r e =>
      simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply]
      rw [← tmul_sum, hdecomp]
    | add y z hy hz =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [hy, hz]
  have hφ : ∀ i, LinearMap.lTensor ℝ ((φ i).restrictScalars ℤ) x = 0 := by
    intro i
    refine realToFibre_integers_eq_zero _ fun σ ↦ ?_
    rw [realToFibre_lTensor, hx σ, map_zero]
  rw [← hdec x]
  simp only [hφ, map_zero, Finset.sum_const_zero]

variable (h : HermitianMetric K E)

def RealSpace (_h : HermitianMetric K E) : Type _ := ℝ ⊗[ℤ] E

namespace RealSpace

instance : AddCommGroup (RealSpace h) := inferInstanceAs (AddCommGroup (ℝ ⊗[ℤ] E))

instance : Module ℝ (RealSpace h) := inferInstanceAs (Module ℝ (ℝ ⊗[ℤ] E))

def equivTensor : RealSpace h ≃ₗ[ℝ] ℝ ⊗[ℤ] E := LinearEquiv.refl ℝ _

@[instance_reducible]
def traceCore : InnerProductSpace.Core ℝ (RealSpace h) where
  inner x y := ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
    (realToFibre σ E (equivTensor h y))).re
  conj_inner_symm x y := by
    rw [conj_trivial]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [← (h.form σ).conj_inner_symm, Complex.conj_re]
  re_inner_nonneg x := by
    rw [RCLike.re_to_real]
    exact Finset.sum_nonneg fun σ _ ↦ (h.form σ).re_inner_nonneg _
  add_left x y z := by
    simp only [map_add, (h.form _).add_left, Complex.add_re, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [map_smul, realToFibre_smul, (h.form _).smul_left, conj_trivial,
      Complex.conj_ofReal, Complex.re_ofReal_mul, Finset.mul_sum]
  definite x hx := by
    have hnn : ∀ σ ∈ Finset.univ, 0 ≤ ((h.form σ).inner (realToFibre σ E (equivTensor h x))
        (realToFibre σ E (equivTensor h x))).re := fun σ _ ↦ (h.form σ).re_inner_nonneg _
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hx
    have := realToFibre_eq_zero (equivTensor h x) fun σ ↦
      core_eq_zero_of_re _ _ (h0 σ (Finset.mem_univ σ))
    exact (equivTensor h).injective (by rw [this, map_zero])

instance : NormedAddCommGroup (RealSpace h) := (traceCore h).toNormedAddCommGroup

instance : InnerProductSpace ℝ (RealSpace h) := InnerProductSpace.ofCore _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inner_def (x y : RealSpace h) :
    inner ℝ x y = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h y))).re := rfl

/- English proof (translation)
Rewrite using `[← real_inner_self_eq_norm_sq, inner_def]`.
-/
theorem norm_sq_eq (x : RealSpace h) :
    ‖x‖ ^ 2 = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h x))).re := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

def ofModule : E →+ RealSpace h := (TensorProduct.mk ℤ ℝ E 1).toAddMonoidHom

def lattice : Submodule ℤ (RealSpace h) := LinearMap.range (ofModule h).toIntLinearMap

/- English proof (translation)
Establish `: Module.Finite ℤ E` using `finite_int K E`. Establish `: Module.Free ℤ E` using `free_int K E`. Use `set bZ := Module.finBasis ℤ E`. Use `⟨_, (Algebra.TensorProduct.basis ℝ bZ).map (equivTensor h).symm, ?_⟩` and prove the remaining obligations. Establish `hb : ⇑((Algebra.TensorProduct.basis ℝ bZ).map (equivTensor h).symm) = (ofModule h).toIntLinearMap ∘ bZ`.

Use function extensionality and compare the values at `i`. Rewrite using `[Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]`. Both sides reduce to the same expression. Rewrite using `[hb, Set.range_comp, ← Submodule.map_span, bZ.span_eq, Submodule.map_top]`. Both sides reduce to the same expression.
-/
theorem exists_basis_lattice_eq :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ (RealSpace h)),
      lattice h = Submodule.span ℤ (Set.range b) := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Free ℤ E := free_int K E
  set bZ := Module.finBasis ℤ E
  refine ⟨_, (Algebra.TensorProduct.basis ℝ bZ).map (equivTensor h).symm, ?_⟩
  have hb : ⇑((Algebra.TensorProduct.basis ℝ bZ).map (equivTensor h).symm) =
      (ofModule h).toIntLinearMap ∘ bZ := by
    funext i
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [hb, Set.range_comp, ← Submodule.map_span, bZ.span_eq, Submodule.map_top]
  rfl

instance : FiniteDimensional ℝ (RealSpace h) := by
  obtain ⟨n, b, -⟩ := exists_basis_lattice_eq h
  exact Module.Finite.of_basis b

instance : DiscreteTopology (lattice h) := by
  obtain ⟨n, b, hb⟩ := exists_basis_lattice_eq h
  rw [hb]
  infer_instance

instance : IsZLattice ℝ (lattice h) where
  span_top := by
    obtain ⟨n, b, hb⟩ := exists_basis_lattice_eq h
    rw [hb, Submodule.span_span_of_tower, b.span_eq]

/- English proof (translation)
Establish `: Module.Finite ℤ E` using `finite_int K E`. Establish `: Module.Free ℤ E` using `free_int K E`. Use `set bZ := Module.finBasis ℤ E`. Introduce `e e' he`. Establish `h1` using `congrArg (Algebra.TensorProduct.basis ℝ bZ).repr (show (1 : ℝ) ⊗ₜ[ℤ] e = (1 : ℝ) ⊗ₜ[ℤ] e' from he)`.

Simplify using `only [Algebra.TensorProduct.basis_repr_tmul, one_smul] at h1`. Conclude with `bZ.repr.injective (Finsupp.mapRange_injective _ _ (algebraMap ℤ ℝ).injective_int h1)`.
-/
theorem ofModule_injective : Function.Injective (ofModule h) := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Free ℤ E := free_int K E
  set bZ := Module.finBasis ℤ E
  intro e e' he
  have h1 := congrArg (Algebra.TensorProduct.basis ℝ bZ).repr
    (show (1 : ℝ) ⊗ₜ[ℤ] e = (1 : ℝ) ⊗ₜ[ℤ] e' from he)
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul] at h1
  exact bZ.repr.injective
    (Finsupp.mapRange_injective _ _ (algebraMap ℤ ℝ).injective_int h1)

end RealSpace

end General

abbrev HermitianBundle.RealSpace (A : HermitianBundle K) : Type _ := Heights.RealSpace A.metric

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : IsZLattice ℝ (RealSpace.lattice (HermitianMetric.standard GaussianField (Fin 2))) :=
  inferInstance

end

end GroundTheory.Heights₂.Heights
