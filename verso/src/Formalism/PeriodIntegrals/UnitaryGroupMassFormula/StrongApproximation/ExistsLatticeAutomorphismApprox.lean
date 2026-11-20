import Mathlib
import Formalism.PeriodIntegrals.StrongApproxE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig p L a e`. Rewrite using `[Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]`.
-/
theorem existsLatticeAutomorphismApprox : LocLin := by
  intro F E _ _ _ _ _ sig p L a e
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig p L n b hb x`. Establish `hsub : Set.range L.ιE ⊆ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i)))`. Introduce and unpack `_ ⟨e, rfl⟩`. Take `⟨c, rfl⟩` from `hb e`. Rewrite using `[map_sum]`.

Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[existsLatticeAutomorphismApprox F E sig p L]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `htop : Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) = ⊤`. Rewrite using `[eq_top_iff, ← L.span]`.

Conclude with `Submodule.span_le.mpr hsub`. Establish `hx : x ∈ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i)))` using `htop ▸ Submodule.mem_top`. Take `⟨α, hα⟩` from `(Submodule.mem_span_range_iff_exists_fun L.Fp).mp hx`. Conclude with `⟨α, hα.symm⟩`.
-/
theorem local_span_holds : LocSpan := by
  intro F E _ _ _ _ _ sig p L n b hb x
  have hsub : Set.range L.ιE ⊆ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨c, rfl⟩ := hb e
    rw [map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [existsLatticeAutomorphismApprox F E sig p L]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) = ⊤ := by
    rw [eq_top_iff, ← L.span]
    exact Submodule.span_le.mpr hsub
  have hx : x ∈ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := htop ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun L.Fp).mp hx
  exact ⟨α, hα.symm⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig p L U hU n w`. Use `L.top` as an intermediate fact. Set `f : Fin n → (L.Fp →+ L.Ep)` to `fun i => (LinearMap.smulRight (LinearMap.id : L.Fp →ₗ[L.Fp] L.Fp) (w i)).toAddMonoidHom`. Establish `hf : ∀ i α, f i α = α • w i` using `fun i α => rfl`. Use `⟨⨅ i, (U.comap (f i)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[AddSubgroup.coe_iInf]`. Use `isOpen_iInter_of_finite (fun i => ?_)` and prove the remaining obligations. Establish `hc : Continuous (f i)`. Establish `: (f i : L.Fp → L.Ep) = fun α => α • w i` using `funext (hf i)`. Rewrite using `[this]`.

Conclude with `continuous_id.smul continuous_const`. Conclude with `hU.preimage hc`. Introduce `α hα i`. Rewrite `hα` using `[AddSubgroup.mem_iInf]`. Use `hα i` as an intermediate fact.

Rewrite `this` using `[AddSubgroup.mem_comap, hf]`. Conclude with `this`.
-/
theorem local_open_subgroup : LocOpen := by
  intro F E _ _ _ _ _ sig p L U hU n w
  have := L.top
  let f : Fin n → (L.Fp →+ L.Ep) := fun i =>
    (LinearMap.smulRight (LinearMap.id : L.Fp →ₗ[L.Fp] L.Fp) (w i)).toAddMonoidHom
  have hf : ∀ i α, f i α = α • w i := fun i α => rfl
  refine ⟨⨅ i, (U.comap (f i)), ?_, ?_⟩
  · rw [AddSubgroup.coe_iInf]
    refine isOpen_iInter_of_finite (fun i => ?_)
    have hc : Continuous (f i) := by
      have : (f i : L.Fp → L.Ep) = fun α => α • w i := funext (hf i)
      rw [this]
      exact continuous_id.smul continuous_const
    exact hU.preimage hc
  · intro α hα i
    rw [AddSubgroup.mem_iInf] at hα
    have := hα i
    rw [AddSubgroup.mem_comap, hf] at this
    exact this

/- English proof (translation)
Introduce `F E _ _ _ _ _`. Establish `: Module.Finite F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Set `B` to `Module.finBasis F E`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image (fun i => B i))`. Use `⟨Module.finrank F E, fun i => y • B i, fun i => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), fun e => ?_⟩` and prove the remaining obligations.

Use `⟨fun i => B.repr e i / (y : F), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← B.sum_repr e]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hyF : (y : F) ≠ 0` using `Int.cast_ne_zero.mpr hy0`. Rewrite using `[smul_comm, ← smul_assoc, zsmul_eq_mul, mul_div_cancel₀ _ hyF]`.
-/
theorem intSpan' : IntSpan := by
  intro F E _ _ _ _ _
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let B := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (fun i => B i))
  refine ⟨Module.finrank F E, fun i => y • B i,
    fun i => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), fun e => ?_⟩
  refine ⟨fun i => B.repr e i / (y : F), ?_⟩
  conv_lhs => rw [← B.sum_repr e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy0
  rw [smul_comm, ← smul_assoc, zsmul_eq_mul, mul_div_cancel₀ _ hyF]

end PI.StrongApproxE
