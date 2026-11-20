import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchPartFinIncl
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.FinInclSmall

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def basisSum : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) →+
    E ⊗[F] FiniteAdeleRing (𝓞 F) F where
  toFun a := ∑ j, ((RingOfIntegers.basis E j : 𝓞 E) : E) ⊗ₜ[F] a j
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

def intSums : AddSubgroup (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).map (basisSum F E)

/- English proof (translation)
Use `⟨fun j => ((RingOfIntegers.basis E).repr o j) • a, fun j _ => zsmul_mem ha _, ?_⟩` and prove the remaining obligations. Establish `ho : (o : E) = ∑ j, ((RingOfIntegers.basis E).repr o j) • ((RingOfIntegers.basis E j : 𝓞 E) : E)` using `by conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr o]`. Use `push_cast`. Both sides reduce to the same expression. Use `show ∑ j, ((RingOfIntegers.basis E j : 𝓞 E) : E) ⊗ₜ[F] (((RingOfIntegers.basis E).repr o j) • a) = _`.

Rewrite using `[ho, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul']`.
-/
theorem tmul_mem_intSums (o : 𝓞 E) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ Formalism.UG.intAd F) :
    (o : E) ⊗ₜ[F] a ∈ intSums F E := by
  refine ⟨fun j => ((RingOfIntegers.basis E).repr o j) • a, fun j _ => zsmul_mem ha _, ?_⟩
  have ho : (o : E) = ∑ j, ((RingOfIntegers.basis E).repr o j) • ((RingOfIntegers.basis E j : 𝓞 E) : E) := by
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr o]
    push_cast
    rfl
  show ∑ j, ((RingOfIntegers.basis E j : 𝓞 E) : E) ⊗ₜ[F] (((RingOfIntegers.basis E).repr o j) • a) = _
  rw [ho, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨o, a, ha, rfl⟩` from `hx`.

Take `⟨o', a', ha', rfl⟩` from `hy`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Conclude with `AddSubgroup.subset_closure ⟨o * o', _, mul_mem ha ha', by push_cast; rfl⟩`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add y y' _ _ h h' => rw [mul_add]`. Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [mul_neg]`. Conclude with `neg_mem h`. Consider the case `zero => rw [zero_mul]`.

Conclude with `zero_mem _`. Consider the case `add x x' _ _ h h' => rw [add_mul]`. Conclude with `add_mem h h'`. Consider the case `neg x _ h => rw [neg_mul]`. Conclude with `neg_mem h`.
-/
theorem mul_mem_intSums {x y : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ AddSubgroup.closure {x | ∃ o : 𝓞 E, ∃ a ∈ Formalism.UG.intAd F, x = (o : E) ⊗ₜ[F] a})
    (hy : y ∈ AddSubgroup.closure {x | ∃ o : 𝓞 E, ∃ a ∈ Formalism.UG.intAd F, x = (o : E) ⊗ₜ[F] a}) :
    x * y ∈ AddSubgroup.closure {x | ∃ o : 𝓞 E, ∃ a ∈ Formalism.UG.intAd F, x = (o : E) ⊗ₜ[F] a} := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨o, a, ha, rfl⟩ := hx
      obtain ⟨o', a', ha', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨o * o', _, mul_mem ha ha', by push_cast; rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

/- English proof (translation)
Establish `hcl : AddSubgroup.closure {x | ∃ o : 𝓞 E, ∃ a ∈ Formalism.UG.intAd F, x = (o : E) ⊗ₜ[F] a} ≤ intSums F E`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨o, a, ha, rfl⟩`. Conclude with `tmul_mem_intSums F E o a ha`. Apply `hcl` to reduce the goal to its premises.

Proceed by induction on `hy using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Conclude with `AddSubgroup.subset_closure ⟨o, 1, one_mem _, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨1, a, a.2, by simp⟩`.

Consider the case `zero => exact zero_mem _`. Consider the case `one => exact AddSubgroup.subset_closure ⟨1, 1, one_mem _, by simp; rfl⟩`. Consider the case `add x y _ _ h h' => exact add_mem h h'`. Consider the case `neg x _ h => exact neg_mem h`. Consider the case `mul x y _ _ h h' => exact mul_mem_intSums F E h h'`.
-/
theorem intAf_le_intSums {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (hy : y ∈ Formalism.MainNotions.S.IntAf F E) :
    y ∈ intSums F E := by
  have hcl : AddSubgroup.closure {x | ∃ o : 𝓞 E, ∃ a ∈ Formalism.UG.intAd F, x = (o : E) ⊗ₜ[F] a} ≤
      intSums F E := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨o, a, ha, rfl⟩
    exact tmul_mem_intSums F E o a ha
  apply hcl
  induction hy using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨a, rfl⟩
    · exact AddSubgroup.subset_closure ⟨o, 1, one_mem _, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, a, a.2, by simp⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, 1, one_mem _, by simp; rfl⟩
  | add x y _ _ h h' => exact add_mem h h'
  | neg x _ h => exact neg_mem h
  | mul x y _ _ h h' => exact mul_mem_intSums F E h h'

end GlobalTheory.FinInclSmall

namespace GlobalTheory.FinInclSmall

/- English proof (translation)
Introduce `F E _ _ _ _ _ U hU`. Use `set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Set `inc : FiniteAdeleRing (𝓞 F) F → AF F` to `fun a => (0, a)`. Establish `hinc : Continuous inc` using `continuous_const.prodMk continuous_id`. Set `φ : (ι → FiniteAdeleRing (𝓞 F) F) → AE F E` to `fun a => ∑ j, inc (a j) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E))`.

Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _`. Establish `hφc : Continuous φ`. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Establish `hj : Continuous fun p : ι → FiniteAdeleRing (𝓞 F) F => p j` using `continuous_apply j`. Conclude with `(hinc.comp hj).smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E) : AE F E)))`.

Establish `hφ0 : φ 0 = 0`. Establish `: inc 0 = 0` using `rfl`. Simplify using `[φ, this]`. Establish `hφU : φ ⁻¹' U ∈ nhds (0 : ι → FiniteAdeleRing (𝓞 F) F)` using `hφc.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact hU)`. Rewrite `hφU` using `[nhds_pi, Filter.mem_pi']`.

Take `⟨I, t, ht, hsub⟩` from `hφU`. Establish `hV : (⋂ j, t j) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F)` using `Filter.iInter_mem.2 ht`. Take `⟨N, hN1, hN⟩` from `Formalism.L2.SG.Pf.top_nhds_basis F _ hV`. Use `⟨N, hN1, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `intAf_le_intSums F E hy`.

Establish `hmem : (fun j => (N : FiniteAdeleRing (𝓞 F) F) * a j) ∈ φ ⁻¹' U` using `hsub fun j _ => Set.mem_iInter.1 (hN (a j) (ha j (Set.mem_univ j))) j`. Establish `e : GlobalTheory.ArchFinSplit.finIncl F E ((N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * basisSum F E a) = φ (fun j => (N : FiniteAdeleRing (𝓞 F) F) * a j)`. Rewrite using `[← nsmul_eq_mul, ← map_nsmul]`. Use `show GlobalTheory.ArchFinSplit.finIncl F E (∑ j, ((RingOfIntegers.basis E j : 𝓞 E) : E) ⊗ₜ[F] (N • a) j) = _`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.ArchFinSplit.finIncl_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hmem`.
-/
theorem finIncl_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∀ U ∈ nhds (0 : AE F E), ∃ N : ℕ, 1 ≤ N ∧ ∀ y ∈ Formalism.MainNotions.S.IntAf F E,
      GlobalTheory.ArchFinSplit.finIncl F E ((N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * y) ∈ U := by
  intro F E _ _ _ _ _ U hU
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let inc : FiniteAdeleRing (𝓞 F) F → AF F := fun a => (0, a)
  have hinc : Continuous inc := continuous_const.prodMk continuous_id
  let φ : (ι → FiniteAdeleRing (𝓞 F) F) → AE F E := fun a =>
    ∑ j, inc (a j) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E))
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hφc : Continuous φ := by
    refine continuous_finset_sum _ fun j _ => ?_
    have hj : Continuous fun p : ι → FiniteAdeleRing (𝓞 F) F => p j := continuous_apply j
    exact (hinc.comp hj).smul (continuous_const (y := ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E) : AE F E)))
  have hφ0 : φ 0 = 0 := by
    have : inc 0 = 0 := rfl
    simp [φ, this]
  have hφU : φ ⁻¹' U ∈ nhds (0 : ι → FiniteAdeleRing (𝓞 F) F) :=
    hφc.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact hU)
  rw [nhds_pi, Filter.mem_pi'] at hφU
  obtain ⟨I, t, ht, hsub⟩ := hφU
  have hV : (⋂ j, t j) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨N, hN1, hN⟩ := Formalism.L2.SG.Pf.top_nhds_basis F _ hV
  refine ⟨N, hN1, fun y hy => ?_⟩
  obtain ⟨a, ha, rfl⟩ := intAf_le_intSums F E hy
  have hmem : (fun j => (N : FiniteAdeleRing (𝓞 F) F) * a j) ∈ φ ⁻¹' U :=
    hsub fun j _ => Set.mem_iInter.1 (hN (a j) (ha j (Set.mem_univ j))) j
  have e : GlobalTheory.ArchFinSplit.finIncl F E ((N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * basisSum F E a) =
      φ (fun j => (N : FiniteAdeleRing (𝓞 F) F) * a j) := by
    rw [← nsmul_eq_mul, ← map_nsmul]
    show GlobalTheory.ArchFinSplit.finIncl F E (∑ j, ((RingOfIntegers.basis E j : 𝓞 E) : E) ⊗ₜ[F] (N • a) j) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.ArchFinSplit.finIncl_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rfl
  rw [e]
  exact hmem

end GlobalTheory.FinInclSmall
