import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.CompletedOrder

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy`. Simplify using `only [add_mul, map_add, add_smul, Finset.sum_add_distrib]`. Rewrite using `[← hx, ← hy]`.

Consider the case `tmul a e`. Establish `h3 : ∀ e : E, Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e)`. Introduce `e`. Establish `h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, smul_eq_mul]`. Use `conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, h3, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, mul_comm a, Algebra.smul_def]`.
-/
theorem eq_sum_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    z = ∑ i, Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b i) • ((1 : R) ⊗ₜ[F] b.traceDual i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | tmul a e =>
    have h3 : ∀ e : E, Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      intro e
      have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, h3, Module.Basis.traceDual_repr_apply,
      Algebra.traceForm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.smul_tmul, mul_comm a, Algebra.smul_def]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h v`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _`. Take `⟨s, b, hb⟩` from `FiniteDimensional.exists_is_basis_integral (𝓞 F) F E`.

Establish `hb' : ∀ i, IsIntegral (v.adicCompletionIntegers F) ((1 : Fv F v) ⊗ₜ[F] b i)`. Introduce `i`. Establish `h1 : IsIntegral ℤ (b i)` using `isIntegral_trans (b i) (hb i)`. Conclude with `h1.map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v)) (RingHom.ext_int _ _)`. Establish `hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`.

Establish `hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v))` using `isCompact_iff_compactSpace.2 (AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)`. Establish `hopen : IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E))`. Set `B` to `Algebra.TensorProduct.basis (Fv F v) b`. Establish `hc : Continuous B.equivFun` using `IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap`. Use `AddSubgroup.isOpen_of_mem_nhds (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup (g := 0) ?_` and prove the remaining obligations.

Use `Filter.mem_of_superset (((isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage hc).mem_nhds ?_) ?_` and prove the remaining obligations. Introduce `i _`. Simplify using the standard rewrite rules. Introduce `z hz show IsIntegral _ z`. Rewrite using `[← B.sum_equivFun z]`.

Use `IsIntegral.sum _ fun i _ => ?_` and prove the remaining obligations. Use `(hb' i).smul (⟨_, hz i (Set.mem_univ i)⟩ : v.adicCompletionIntegers F)` as an intermediate fact. Rewrite using `[Algebra.TensorProduct.basis_apply]`. Conclude with `this`. Use `⟨?_, hopen⟩` and prove the remaining obligations.

Establish `hclosed : IsClosed (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E))` using `AddSubgroup.isClosed_of_isOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup hopen`. Establish `hcont : Continuous fun x : s → Fv F v => ∑ i, x i • ((1 : Fv F v) ⊗ₜ[F] b.traceDual i)` using `by fun_prop`. Use `IsCompact.of_isClosed_subset ((isCompact_univ_pi fun _ => hC).image hcont) hclosed ?_` and prove the remaining obligations. Introduce `z hz`. Use `⟨_, ?_, (eq_sum_trace b (Fv F v) z).symm⟩` and prove the remaining obligations.

Introduce `i _`. Establish `h1 : IsIntegral (v.adicCompletionIntegers F) (z * (1 : Fv F v) ⊗ₜ[F] b i)` using `IsIntegral.mul hz (hb' i)`. Establish `h2 : IsIntegral (v.adicCompletionIntegers F) (sigR (Fv F v) σ (z * (1 : Fv F v) ⊗ₜ[F] b i))` using `h1.map ((Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).restrictScalars (v.adicCompletionIntegers F))`. Establish `h3` using `h1.add h2`. Rewrite `h3` using `[← SelfDualLatticeCompare.trace_tensor (Fv F v) h, isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)]`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h3`. Use `beta_reduce`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem isCompact_isOpen_integralClosure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h v
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral (v.adicCompletionIntegers F) ((1 : Fv F v) ⊗ₜ[F] b i) := by
    intro i
    have h1 : IsIntegral ℤ (b i) := isIntegral_trans (b i) (hb i)
    exact h1.map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
      (RingHom.ext_int _ _)
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have hopen : IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :
      Set (Fv F v ⊗[F] E)) := by
    let B := Algebra.TensorProduct.basis (Fv F v) b
    have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
    refine AddSubgroup.isOpen_of_mem_nhds
      (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup
      (g := 0) ?_
    refine Filter.mem_of_superset (((isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage hc).mem_nhds ?_) ?_
    · intro i _
      simp
    · intro z hz
      show IsIntegral _ z
      rw [← B.sum_equivFun z]
      refine IsIntegral.sum _ fun i _ => ?_
      have := (hb' i).smul (⟨_, hz i (Set.mem_univ i)⟩ : v.adicCompletionIntegers F)
      rw [Algebra.TensorProduct.basis_apply]
      exact this
  refine ⟨?_, hopen⟩
  have hclosed : IsClosed (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :
      Set (Fv F v ⊗[F] E)) :=
    AddSubgroup.isClosed_of_isOpen
      (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup hopen
  have hcont : Continuous fun x : s → Fv F v => ∑ i, x i • ((1 : Fv F v) ⊗ₜ[F] b.traceDual i) := by
    fun_prop
  refine IsCompact.of_isClosed_subset ((isCompact_univ_pi fun _ => hC).image hcont) hclosed ?_
  intro z hz
  refine ⟨_, ?_, (eq_sum_trace b (Fv F v) z).symm⟩
  intro i _
  have h1 : IsIntegral (v.adicCompletionIntegers F) (z * (1 : Fv F v) ⊗ₜ[F] b i) :=
    IsIntegral.mul hz (hb' i)
  have h2 : IsIntegral (v.adicCompletionIntegers F) (sigR (Fv F v) σ (z * (1 : Fv F v) ⊗ₜ[F] b i)) :=
    h1.map ((Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).restrictScalars
      (v.adicCompletionIntegers F))
  have h3 := h1.add h2
  rw [← SelfDualLatticeCompare.trace_tensor (Fv F v) h,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)] at h3
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  beta_reduce
  rw [← hy]
  exact y.2

end GlobalTheory.CompletedOrder
