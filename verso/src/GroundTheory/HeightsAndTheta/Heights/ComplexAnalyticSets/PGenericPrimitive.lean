import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

open MvPolynomial

def linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) : MvPolynomial (Fin n) k :=
  ∑ j, C (φ (Pi.single j 1)) * X j

/- English proof (translation)
Establish `hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k)`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hc]`. Simplify using `[linearFormPoly, map_sum, mul_comm]`.
-/
theorem eval_linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  simp [linearFormPoly, map_sum, mul_comm]

/- English proof (translation)
Introduce `k K L _ _ _ _ _ _ _ _ _ n x hx`. Establish `hfin : Finite (IntermediateField K L)` using `Field.finite_intermediateField_of_exists_primitive_element K L (Field.exists_primitive_element K L)`. Use `Fintype.ofFinite (IntermediateField K L)` as an intermediate fact. Set `f : (Fin n → k) →ₗ[k] L` to `Fintype.linearCombination k x`. Establish `hf : ∀ c, f c = ∑ j, c j • x j` using `fun c => Fintype.linearCombination_apply k x c`.

Set `W : IntermediateField K L → Submodule k (Fin n → k)` to `fun M => (M.toSubalgebra.toSubmodule.restrictScalars k).comap f`. Establish `hW : ∀ M : IntermediateField K L, M ≠ ⊤ → W M < ⊤`. Introduce `M hM`. Use `lt_top_iff_ne_top.2 fun htop => hM ?_` and prove the remaining obligations. Establish `hxM : Set.range x ⊆ M`.

Introduce and unpack `_ ⟨j, rfl⟩`. Establish `hj : (Pi.single j 1 : Fin n → k) ∈ W M` using `htop ▸ Submodule.mem_top`. Establish `: f (Pi.single j 1) = x j`. Rewrite using `[hf]`. Simplify using `[Pi.single_apply]`.

Simplify `hj` using `[W, this]`. Conclude with `eq_top_iff.2 (hx ▸ IntermediateField.adjoin_le_iff.2 hxM)`. Establish `hφ : ∀ M : IntermediateField K L, ∃ φ : (Fin n → k) →ₗ[k] k, M ≠ ⊤ → φ ≠ 0 ∧ W M ≤ LinearMap.ker φ`. Introduce `M`. Distinguish the cases in `hM : M = ⊤`.

Conclude with `⟨0, fun h => (h hM).elim⟩`. Take `⟨φ, h0, hle⟩` from `(W M).exists_le_ker_of_lt_top (hW M hM)`. Conclude with `⟨φ, fun _ => ⟨h0, hle⟩⟩`. Use `choose φ hφ using hφ`. Set `S : Finset (IntermediateField K L)` to `Finset.univ.filter (· ≠ ⊤)`.

Use `⟨∏ M ∈ S, linearFormPoly (φ M), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `M hM`. Establish `hM' : M ≠ ⊤` using `(Finset.mem_filter.1 hM).2`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, φ M c ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Conclude with `(hφ M hM').1 (LinearMap.ext fun c => by simpa using not_not.1 (not_exists.1 h c))`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← eval_linearFormPoly, h0, map_zero]`.

Introduce `c hc`. Assume the negation of the conclusion as `hne`. Rewrite `hc` using `[map_prod, Finset.prod_ne_zero_iff]`. Establish `hmem : IntermediateField.adjoin K {∑ j, c j • x j} ∈ S` using `Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩`. Apply `hc _ hmem` to reduce the goal to its premises.

Rewrite using `[eval_linearFormPoly]`. Apply `(hφ _ hne).2` to reduce the goal to its premises. Use `show f c ∈ IntermediateField.adjoin K {∑ j, c j • x j}`. Rewrite using `[hf]`. Conclude with `IntermediateField.mem_adjoin_simple_self K _`.
-/
theorem GenericPrimitive.proof : GenericPrimitive.Statement := by
  intro k K L _ _ _ _ _ _ _ _ _ n x hx
  have hfin : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L (Field.exists_primitive_element K L)
  have := Fintype.ofFinite (IntermediateField K L)
  classical

  let f : (Fin n → k) →ₗ[k] L := Fintype.linearCombination k x
  have hf : ∀ c, f c = ∑ j, c j • x j := fun c => Fintype.linearCombination_apply k x c

  let W : IntermediateField K L → Submodule k (Fin n → k) := fun M =>
    (M.toSubalgebra.toSubmodule.restrictScalars k).comap f
  have hW : ∀ M : IntermediateField K L, M ≠ ⊤ → W M < ⊤ := by
    intro M hM
    refine lt_top_iff_ne_top.2 fun htop => hM ?_
    have hxM : Set.range x ⊆ M := by
      rintro _ ⟨j, rfl⟩
      have hj : (Pi.single j 1 : Fin n → k) ∈ W M := htop ▸ Submodule.mem_top
      have : f (Pi.single j 1) = x j := by
        rw [hf]; simp [Pi.single_apply]
      simpa [W, this] using hj
    exact eq_top_iff.2 (hx ▸ IntermediateField.adjoin_le_iff.2 hxM)
  have hφ : ∀ M : IntermediateField K L, ∃ φ : (Fin n → k) →ₗ[k] k,
      M ≠ ⊤ → φ ≠ 0 ∧ W M ≤ LinearMap.ker φ := by
    intro M
    by_cases hM : M = ⊤
    · exact ⟨0, fun h => (h hM).elim⟩
    · obtain ⟨φ, h0, hle⟩ := (W M).exists_le_ker_of_lt_top (hW M hM)
      exact ⟨φ, fun _ => ⟨h0, hle⟩⟩
  choose φ hφ using hφ
  let S : Finset (IntermediateField K L) := Finset.univ.filter (· ≠ ⊤)
  refine ⟨∏ M ∈ S, linearFormPoly (φ M), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    have hM' : M ≠ ⊤ := (Finset.mem_filter.1 hM).2
    obtain ⟨c, hc⟩ : ∃ c, φ M c ≠ 0 := by
      by_contra h
      exact (hφ M hM').1 (LinearMap.ext fun c => by simpa using not_not.1 (not_exists.1 h c))
    intro h0
    apply hc
    rw [← eval_linearFormPoly, h0, map_zero]
  · intro c hc
    by_contra hne
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    have hmem : IntermediateField.adjoin K {∑ j, c j • x j} ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
    apply hc _ hmem
    rw [eval_linearFormPoly]
    apply (hφ _ hne).2
    show f c ∈ IntermediateField.adjoin K {∑ j, c j • x j}
    rw [hf]
    exact IntermediateField.mem_adjoin_simple_self K _

end

end GroundTheory.Heights₂.Heights.ComplexSets
