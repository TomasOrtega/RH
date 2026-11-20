import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TraceSum

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

section SlopeTestRemainingChoices

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `hcl : E.topologicalClosure = E` using `(Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq`. Use `haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance`. Establish `h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL)`. Rewrite using `[isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]`. Conclude with `ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top`.

Conclude with `h1.comp_right E.topologicalClosure.orthogonalProjection`.
-/
private theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjection

/- English proof (translation)
Simplify using `[eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]`.
-/
private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

/- English proof (translation)
Establish `h : prj V v ∈ V.topologicalClosure` using `Submodule.starProjection_apply_mem _ v`. Rewrite `h` using `[hV.submodule_topologicalClosure_eq]`. Then use the resulting hypothesis.
-/
private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hV.submodule_topologicalClosure_eq] at h

/- English proof (translation)
The claim follows from `(Submodule.starProjection_apply_eq_zero_iff _).2 (by rwa [Submodule.orthogonal_closure])`.
-/
private theorem prj_eq_zero {V : Submodule ℂ H} {v : H} (hv : v ∈ Vᗮ) : prj V v = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).2 (by rwa [Submodule.orthogonal_closure])

/- English proof (translation)
The claim follows from `Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)`.
-/
private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

/- English proof (translation)
Establish `h` using `Submodule.sub_starProjection_mem_orthogonal (K := V.topologicalClosure) v`. Rewrite `h` using `[Submodule.orthogonal_closure]`. Then use the resulting hypothesis.
-/
private theorem sub_prj_mem (V : Submodule ℂ H) (v : H) : v - prj V v ∈ Vᗮ := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := V.topologicalClosure) v
  rwa [Submodule.orthogonal_closure] at h

/- English proof (translation)
Establish `hu` using `sub_prj_mem V v`. Establish `hadj : ContinuousLinearMap.adjoint A = A` using `(ContinuousLinearMap.isSelfAdjoint_iff').1 hA`. Establish `hAu : A (v - prj V v) ∈ Vᗮ`. Rewrite `hu`, the goal using `[Submodule.mem_orthogonal]`. Introduce `w hw`.

Rewrite using `[← ContinuousLinearMap.adjoint_inner_left, hadj]`. Conclude with `hu _ (hinv w hw)`. Establish `h : A v = A (prj V v) + A (v - prj V v)`. Rewrite using `[← map_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[h, map_add, prj_eq_zero hAu, add_zero, prj_self (hinv _ (prj_mem hV v))]`.
-/
private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (hinv : ∀ v ∈ V, A v ∈ V) (v : H) : prj V (A v) = A (prj V v) := by
  have hu := sub_prj_mem V v
  have hadj : ContinuousLinearMap.adjoint A = A := (ContinuousLinearMap.isSelfAdjoint_iff').1 hA
  have hAu : A (v - prj V v) ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
    exact hu _ (hinv w hw)
  have h : A v = A (prj V v) + A (v - prj V v) := by
    rw [← map_add]; congr 1; abel
  rw [h, map_add, prj_eq_zero hAu, add_zero, prj_self (hinv _ (prj_mem hV v))]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `H ι _ _ _ V W A x hc ho hW hA hinv hfd`. Set `E : ι → Submodule ℂ H` to `fun i => eigIn (V i) A x`. Establish `hVW : ∀ i, V i ≤ W` using `fun i => hW ▸ (le_iSup V i).trans (Submodule.le_topologicalClosure _)`. Establish `hEW : ∀ i, E i ≤ eigIn W A x` using `fun i => inf_le_inf_right _ (hVW i)`. Establish `hEV : ∀ i, E i ≤ V i` using `fun i => inf_le_left`.

Establish `hEo : Pairwise fun i j => E i ⟂ E j` using `fun i j hij => (ho hij).mono (hEV i) (hEV j)`. Establish `hfin : {i | E i ≠ ⊥}.Finite`. Establish `hex : ∀ i : {i | E i ≠ ⊥}, ∃ v ∈ E i, v ≠ 0` using `fun i => (Submodule.ne_bot_iff _).1 i.2`. Use `choose v hvE hv0 using hex`. Establish `hli : LinearIndependent ℂ v` using `linearIndependent_of_ne_zero_of_inner_eq_zero hv0 fun i j hij => (hEo fun e => hij (Subtype.ext e)).inner_eq (hvE i) (hvE j)`.

Set `v' : {i | E i ≠ ⊥} → eigIn W A x` to `fun i => ⟨v i, hEW i (hvE i)⟩`. Establish `hli' : LinearIndependent ℂ v'` using `LinearIndependent.of_comp (eigIn W A x).subtype hli`. Conclude with `Set.finite_coe_iff.1 hli'.finite_of_isNoetherian`. Set `s` to `hfin.toFinset`. Establish `hs : ∀ i, i ∈ s ↔ E i ≠ ⊥` using `fun i => by simp [s]`.

Establish `hPE : ∀ i, ∀ v ∈ eigIn W A x, prj (V i) v ∈ E i`. Introduce `i v hv`. Use `mem_eigIn.2 ⟨prj_mem (hc i) v, ?_⟩` and prove the remaining obligations. Rewrite using `[← prj_comm (hc i) hA (hinv i), (mem_eigIn.1 hv).2, map_smul]`. Establish `hPP : ∀ i j, i ≠ j → ∀ v, prj (V j) (prj (V i) v) = 0` using `fun i j hij v => prj_eq_zero ((ho hij) (prj_mem (hc i) v))`.

Establish `hsup : eigIn W A x = ⨆ i ∈ s, E i`. Use `le_antisymm (fun v hv => ?_) (iSup₂_le fun i _ => hEW i)` and prove the remaining obligations. Establish `hu : ∑ i ∈ s, prj (V i) v ∈ ⨆ i ∈ s, E i` using `Submodule.sum_mem _ fun i hi => (le_iSup₂_of_le i hi le_rfl : E i ≤ ⨆ i ∈ s, E i) (hPE i v hv)`. Establish `huE : ∑ i ∈ s, prj (V i) v ∈ eigIn W A x` using `(iSup₂_le fun i _ => hEW i : (⨆ i ∈ s, E i) ≤ eigIn W A x) hu`. Establish `hw : v - ∑ i ∈ s, prj (V i) v ∈ W` using `sub_mem (mem_eigIn.1 hv).1 (mem_eigIn.1 huE).1`.

Establish `hPw : ∀ j, prj (V j) (v - ∑ i ∈ s, prj (V i) v) = 0`. Introduce `j`. Rewrite using `[map_sub, map_sum]`. Distinguish the cases in `hj : j ∈ s`. Rewrite using `[Finset.sum_eq_single_of_mem j hj (fun i _ hij => hPP i j hij v), prj_self (prj_mem (hc j) v), sub_self]`.

Establish `h0 : prj (V j) v = 0`. Establish `hb : E j = ⊥` using `by_contra fun h => hj ((hs j).2 h)`. Establish `h1` using `hPE j v hv`. Rewrite `h1` using `[hb]`. Conclude with `(Submodule.mem_bot ℂ).1 h1`.

Rewrite using `[h0, Finset.sum_eq_zero (fun i hi => hPP i j (ne_of_mem_of_not_mem hi hj) v), sub_zero]`. Establish `hperp : v - ∑ i ∈ s, prj (V i) v ∈ Wᗮ`. Rewrite using `[← hW, Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]`. Introduce `j`. Establish `h` using `sub_prj_mem (V j) (v - ∑ i ∈ s, prj (V i) v)`.

Rewrite `h` using `[hPw j, sub_zero]`. Then use the resulting hypothesis. Establish `hz : v - ∑ i ∈ s, prj (V i) v = 0` using `inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hperp _ hw)`. Rewrite using `[sub_eq_zero.1 hz]`. Conclude with `hu`. Use `⟨s, hs, hsup, fun T => ?_⟩` and prove the remaining obligations.

Establish `hS : (⨆ i : s, E i) = eigIn W A x`. Rewrite using `[hsup, iSup_subtype']`. Establish `htc : IsTraceClass (prj (⨆ i : s, E i) ∘L T ∘L prj (⨆ i : s, E i))`. Rewrite using `[hS]`. Conclude with `isTraceClass_comp (isHS_prj _) ((isHS_prj _).comp_left T)`.

Establish `h` using `UpperTheory.ConvolutionTheory.C.traceSum H s (fun i => E i) T (fun i j hij => hEo fun e => hij (Subtype.ext e)) htc`. Rewrite `h` using `[hS]`. Rewrite using `[h.unique (hasSum_fintype _)]`. Conclude with `Finset.sum_coe_sort s fun i => trOn (E i) T`.
-/
theorem UpperTheory.ConvolutionTheory.C.eigSummands :
    UpperTheory.ConvolutionTheory.C.EigSummands := by
  intro H ι _ _ _ V W A x hc ho hW hA hinv hfd
  classical
  let E : ι → Submodule ℂ H := fun i => eigIn (V i) A x
  have hVW : ∀ i, V i ≤ W := fun i => hW ▸ (le_iSup V i).trans (Submodule.le_topologicalClosure _)
  have hEW : ∀ i, E i ≤ eigIn W A x := fun i => inf_le_inf_right _ (hVW i)
  have hEV : ∀ i, E i ≤ V i := fun i => inf_le_left
  have hEo : Pairwise fun i j => E i ⟂ E j := fun i j hij => (ho hij).mono (hEV i) (hEV j)
  have hfin : {i | E i ≠ ⊥}.Finite := by
    have hex : ∀ i : {i | E i ≠ ⊥}, ∃ v ∈ E i, v ≠ 0 := fun i => (Submodule.ne_bot_iff _).1 i.2
    choose v hvE hv0 using hex
    have hli : LinearIndependent ℂ v := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 fun i j hij =>
      (hEo fun e => hij (Subtype.ext e)).inner_eq (hvE i) (hvE j)
    let v' : {i | E i ≠ ⊥} → eigIn W A x := fun i => ⟨v i, hEW i (hvE i)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp (eigIn W A x).subtype hli
    exact Set.finite_coe_iff.1 hli'.finite_of_isNoetherian
  let s := hfin.toFinset
  have hs : ∀ i, i ∈ s ↔ E i ≠ ⊥ := fun i => by simp [s]
  have hPE : ∀ i, ∀ v ∈ eigIn W A x, prj (V i) v ∈ E i := by
    intro i v hv
    refine mem_eigIn.2 ⟨prj_mem (hc i) v, ?_⟩
    rw [← prj_comm (hc i) hA (hinv i), (mem_eigIn.1 hv).2, map_smul]
  have hPP : ∀ i j, i ≠ j → ∀ v, prj (V j) (prj (V i) v) = 0 := fun i j hij v =>
    prj_eq_zero ((ho hij) (prj_mem (hc i) v))
  have hsup : eigIn W A x = ⨆ i ∈ s, E i := by
    refine le_antisymm (fun v hv => ?_) (iSup₂_le fun i _ => hEW i)
    have hu : ∑ i ∈ s, prj (V i) v ∈ ⨆ i ∈ s, E i :=
      Submodule.sum_mem _ fun i hi => (le_iSup₂_of_le i hi le_rfl : E i ≤ ⨆ i ∈ s, E i) (hPE i v hv)
    have huE : ∑ i ∈ s, prj (V i) v ∈ eigIn W A x :=
      (iSup₂_le fun i _ => hEW i : (⨆ i ∈ s, E i) ≤ eigIn W A x) hu
    have hw : v - ∑ i ∈ s, prj (V i) v ∈ W := sub_mem (mem_eigIn.1 hv).1 (mem_eigIn.1 huE).1
    have hPw : ∀ j, prj (V j) (v - ∑ i ∈ s, prj (V i) v) = 0 := by
      intro j
      rw [map_sub, map_sum]
      by_cases hj : j ∈ s
      · rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => hPP i j hij v), prj_self (prj_mem (hc j) v), sub_self]
      · have h0 : prj (V j) v = 0 := by
          have hb : E j = ⊥ := by_contra fun h => hj ((hs j).2 h)
          have h1 := hPE j v hv
          rw [hb] at h1
          exact (Submodule.mem_bot ℂ).1 h1
        rw [h0, Finset.sum_eq_zero (fun i hi => hPP i j (ne_of_mem_of_not_mem hi hj) v), sub_zero]
    have hperp : v - ∑ i ∈ s, prj (V i) v ∈ Wᗮ := by
      rw [← hW, Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro j
      have h := sub_prj_mem (V j) (v - ∑ i ∈ s, prj (V i) v)
      rwa [hPw j, sub_zero] at h
    have hz : v - ∑ i ∈ s, prj (V i) v = 0 :=
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hperp _ hw)
    rw [sub_eq_zero.1 hz]
    exact hu
  refine ⟨s, hs, hsup, fun T => ?_⟩
  have hS : (⨆ i : s, E i) = eigIn W A x := by
    rw [hsup, iSup_subtype']
  have htc : IsTraceClass (prj (⨆ i : s, E i) ∘L T ∘L prj (⨆ i : s, E i)) := by
    rw [hS]
    exact isTraceClass_comp (isHS_prj _) ((isHS_prj _).comp_left T)
  have h := UpperTheory.ConvolutionTheory.C.traceSum H s (fun i => E i) T (fun i j hij => hEo fun e => hij (Subtype.ext e)) htc
  rw [hS] at h
  rw [h.unique (hasSum_fintype _)]
  exact Finset.sum_coe_sort s fun i => trOn (E i) T
