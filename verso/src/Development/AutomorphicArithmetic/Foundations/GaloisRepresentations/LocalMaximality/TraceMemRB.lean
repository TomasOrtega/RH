import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K'] {d : ℕ}

/- English proof (translation)
The claim follows from `.of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply F K K' (r : F)`.
-/
private theorem tower_rA (y : Fin (d + 1) → F) : IsScalarTower (rA ℂ y {0}) K K' :=
  .of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply F K K' (r : F)

/- English proof (translation)
Rewrite `hb`, the goal using `[rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Use `haveI := tower_rA (K := K) (K' := K') y`. Conclude with `hb.algebraMap`.
-/
private theorem map_mem_rB (y : Fin (d + 1) → F) {b : K} (hb : b ∈ rB ℂ K y {0}) :
    algebraMap K K' b ∈ rB ℂ K' y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hb ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact hb.algebraMap

/- English proof (translation)
Rewrite `hv`, the goal using `[rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Use `haveI := tower_rA (K := K) (K' := K') y`. Conclude with `Algebra.isIntegral_trace hv`.
-/
private theorem trace_mem_rB (y : Fin (d + 1) → F) [FiniteDimensional K K'] {v : K'}
    (hv : v ∈ rB ℂ K' y {0}) : Algebra.trace K K' v ∈ rB ℂ K y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hv ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact Algebra.isIntegral_trace hv

end

/- English proof (translation)
Introduce `F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY`. Use `haveI : FiniteDimensional F K' := hY.covY.fin`. Use `haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite F K K'`. Establish `hred` using `hY.red`. Unfold `RedFib at hred ⊢`.

Prove the components needed by the constructor for the conclusion. Introduce `z hz`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨n, hn⟩` from `hz`. Rewrite `hn` using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]`.

Take `⟨c, hc⟩` from `hn`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `set t : Fin d → F := fun j => xv x j.succ / xv x 0 with ht`. Establish `hcK : ∑ j, (c j : K) * algebraMap F K (t j) = (a : K) ^ n`. Use `congrArg (fun u : rB ℂ K (xv x) {0} => (u : K)) hc` as an intermediate fact.

Simplify `this` using `only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]`. Set `b : rB ℂ K' (xv x) {0}` to `⟨algebraMap K K' a, map_mem_rB (xv x) a.2⟩`. Establish `hb : b ∈ Ideal.span (Set.range fun j : Fin d => (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))`. Establish `hq : IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d => (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))) b)`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]`. Use `⟨fun j => ⟨algebraMap K K' (c j), map_mem_rB (xv x) (c j).2⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [b, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]`. Rewrite using `[← map_pow, ← hcK, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← IsScalarTower.algebraMap_apply]`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem).1 (hred.eq_zero _ hq)`. Rewrite `hb` using `[Ideal.mem_span_range_iff_exists_fun]`. Take `⟨e, he⟩` from `hb`.

Establish `key : (Module.finrank K K' : K) * (a : K) = ∑ j, Algebra.trace K K' (e j : K') * algebraMap F K (t j)`. Establish `h1` using `congrArg (fun u : rB ℂ K' (xv x) {0} => Algebra.trace K K' (u : K')) he`. Simplify using `only [b, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, map_sum, Algebra.trace_algebraMap, nsmul_eq_mul] at h1`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_apply F K K', mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Establish `hmem : ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) ∈ Ideal.span (Set.range fun j : Fin d => (⟨algebraMap F K (t j), tco_mem ℂ K (xv x) j⟩ : rB ℂ K (xv x) {0}))`. Rewrite using `[Ideal.mem_span_range_iff_exists_fun]`. Use `⟨fun j => ⟨Algebra.trace K K' (e j : K'), trace_mem_rB (xv x) (e j).2⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubringClass.coe_natCast]`. Conclude with `key.symm`. Establish `hpos : (Module.finrank K K' : ℂ) ≠ 0`. Conclude with `(Module.finrank_pos (R := K) (M := K')).ne'` after adjusting the coercions. Establish `hA : a = algebraMap ℂ (rB ℂ K (xv x) {0}) ((Module.finrank K K' : ℂ)⁻¹) * ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a)`.

Rewrite using `[← mul_assoc, ← map_natCast (algebraMap ℂ (rB ℂ K (xv x) {0})), ← map_mul, inv_mul_cancel₀ hpos, map_one, one_mul]`. Rewrite using `[hA]`. Conclude with `Ideal.mul_mem_left _ _ hmem`.
-/
theorem UpperTheory.Gal.productCup_of_system.redK_of :
    RedK := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite F K K'
  have hred := hY.red
  unfold RedFib at hred ⊢
  constructor
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Ideal.Quotient.eq_zero_iff_mem]
  set t : Fin d → F := fun j => xv x j.succ / xv x 0 with ht
  have hcK : ∑ j, (c j : K) * algebraMap F K (t j) = (a : K) ^ n := by
    have := congrArg (fun u : rB ℂ K (xv x) {0} => (u : K)) hc
    simpa only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow] using this
  let b : rB ℂ K' (xv x) {0} := ⟨algebraMap K K' a, map_mem_rB (xv x) a.2⟩
  have hb : b ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0})) := by
    have hq : IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
        (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))) b) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun j => ⟨algebraMap K K' (c j), map_mem_rB (xv x) (c j).2⟩, ?_⟩
      apply Subtype.ext
      simp only [b, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [← map_pow, ← hcK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (hred.eq_zero _ hq)
  rw [Ideal.mem_span_range_iff_exists_fun] at hb
  obtain ⟨e, he⟩ := hb
  have key : (Module.finrank K K' : K) * (a : K) =
      ∑ j, Algebra.trace K K' (e j : K') * algebraMap F K (t j) := by
    have h1 := congrArg (fun u : rB ℂ K' (xv x) {0} => Algebra.trace K K' (u : K')) he
    simp only [b, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, map_sum,
      Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply F K K', mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
      mul_comm]
  have hmem : ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K (t j), tco_mem ℂ K (xv x) j⟩ : rB ℂ K (xv x) {0})) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => ⟨Algebra.trace K K' (e j : K'), trace_mem_rB (xv x) (e j).2⟩, ?_⟩
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubringClass.coe_natCast]
    exact key.symm
  have hpos : (Module.finrank K K' : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hA : a = algebraMap ℂ (rB ℂ K (xv x) {0}) ((Module.finrank K K' : ℂ)⁻¹) *
      ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ (rB ℂ K (xv x) {0})), ← map_mul,
      inv_mul_cancel₀ hpos, map_one, one_mul]
  rw [hA]
  exact Ideal.mul_mem_left _ _ hmem
