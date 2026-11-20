import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRelAlgClosureFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IntermediateField.algebraAdjoinAdjoin

/- English proof (translation)
Rewrite `hm`, the goal using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Establish `hp : ∀ j, ∃ p : MvPolynomial σ K, aeval x p = (g j : L)` using `fun j => by`. Establish `h : (g j : L) ∈ (aeval x : MvPolynomial σ K →ₐ[K] L).range`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`.

Conclude with `(g j).2`. Conclude with `(AlgHom.mem_range _).1 h`. Use `choose p hp using hp`. Establish `hP : (∑ j ∈ s, C (m j) * map (algebraMap K M) (p j) : MvPolynomial σ M) = 0`. Apply `hx.eq_zero_of_aeval_eq_zero` to reduce the goal to its premises.

Rewrite using `[← hg]`. Simplify using `only [map_sum, map_mul, aeval_C, aeval_map_algebraMap, hp]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.

Establish `hcoeff : ∀ d, ∀ j ∈ s, coeff d (p j) = 0` using `fun d => by`. Apply `hm s (fun j => coeff d (p j))` to reduce the goal to its premises. Use `congrArg (coeff d) hP` as an intermediate fact. Simplify using `only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at this`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Establish `hpi : p i = 0` using `MvPolynomial.ext _ _ fun d => by rw [hcoeff d i hi, coeff_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hp i, hpi, map_zero]`.

Both sides reduce to the same expression.
-/
theorem RelAlgClosureFinite.linearIndependent_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) {σ : Type*} {x : σ → L} (hx : AlgebraicIndependent M x)
    {ι : Type*} {m : ι → M} (hm : LinearIndependent K m) :
    LinearIndependent (Algebra.adjoin K (Set.range x)) (fun i => (m i : L)) := by
  rw [linearIndependent_iff'] at hm ⊢
  intro s g hg i hi
  have hp : ∀ j, ∃ p : MvPolynomial σ K, aeval x p = (g j : L) := fun j => by
    have h : (g j : L) ∈ (aeval x : MvPolynomial σ K →ₐ[K] L).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (g j).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hp
  have hP : (∑ j ∈ s, C (m j) * map (algebraMap K M) (p j) : MvPolynomial σ M) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    rw [← hg]
    simp only [map_sum, map_mul, aeval_C, aeval_map_algebraMap, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  have hcoeff : ∀ d, ∀ j ∈ s, coeff d (p j) = 0 := fun d => by
    apply hm s (fun j => coeff d (p j))
    have := congrArg (coeff d) hP
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := MvPolynomial.ext _ _ fun d => by rw [hcoeff d i hi, coeff_zero]
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

/- English proof (translation)
Introduce `K L _ _ _ S hS`. Take `⟨t, ht⟩` from `exists_isTranscendenceBasis K L`. Use `set M := algebraicClosure K L`. Establish `hM : AlgebraicIndependent M ((↑) : t → L)` using `ht.1.algebraicClosure`. Use `set E := IntermediateField.adjoin K (Set.range ((↑) : t → L))`.

Establish `halg : Algebra.IsAlgebraic E L` using `ht.isAlgebraic_field`. Establish `htop : IntermediateField.adjoin E (S : Set L) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Establish `hz : z ∈ IntermediateField.adjoin K (S : Set L)` using `hS ▸ IntermediateField.mem_top`.

Establish `hle : IntermediateField.adjoin K (S : Set L) ≤ (IntermediateField.adjoin E (S : Set L)).restrictScalars K` using `IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin E _ hy`. Conclude with `hle hz`. Establish `hfin : FiniteDimensional E L`. Establish `h` using `IntermediateField.finiteDimensional_adjoin (K := E) (S := (S : Set L)) fun y _ => (halg.isAlgebraic y).isIntegral`. Rewrite `h` using `[htop]`.

Conclude with `(IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional`. Set `b` to `Module.Basis.ofVectorSpace K M`. Establish `hli : LinearIndependent E (fun i => ((b i : M) : L))` using `(LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range ((↑) : t → L))) E).1 (RelAlgClosureFinite.linearIndependent_adjoin M hM b.linearIndependent)`. Establish `: Finite (Module.Basis.ofVectorSpaceIndex K M)` using `hli.finite`. Conclude with `Module.Finite.of_basis b`.
-/
theorem RelAlgClosureFinite.proof : RelAlgClosureFinite.Statement := by
  intro K L _ _ _ S hS
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  set M := algebraicClosure K L
  have hM : AlgebraicIndependent M ((↑) : t → L) := ht.1.algebraicClosure
  set E := IntermediateField.adjoin K (Set.range ((↑) : t → L))
  have halg : Algebra.IsAlgebraic E L := ht.isAlgebraic_field
  have htop : IntermediateField.adjoin E (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K (S : Set L) := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K (S : Set L) ≤
        (IntermediateField.adjoin E (S : Set L)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin E _ hy
    exact hle hz
  have hfin : FiniteDimensional E L := by
    have h := IntermediateField.finiteDimensional_adjoin (K := E) (S := (S : Set L))
      fun y _ => (halg.isAlgebraic y).isIntegral
    rw [htop] at h
    exact (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional
  let b := Module.Basis.ofVectorSpace K M
  have hli : LinearIndependent E (fun i => ((b i : M) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range ((↑) : t → L))) E).1
      (RelAlgClosureFinite.linearIndependent_adjoin M hM b.linearIndependent)
  have : Finite (Module.Basis.ofVectorSpaceIndex K M) := hli.finite
  exact Module.Finite.of_basis b

end GroundTheory.Heights₂.Heights.Inter
