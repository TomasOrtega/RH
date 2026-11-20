import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Use `⟨if i = j then 1 else 0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`.

Conclude with `⟨c * a, by rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]⟩`.
-/
theorem standard_coord_integral {m : ℕ} {v : Fin m → K}
    (hv : v ∈ (HermLattice.standard K m).lattice) (i : Fin m) :
    ∃ b : 𝓞 K, v i = algebraMap (𝓞 K) K b := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨if i = j then 1 else 0, ?_⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]⟩

omit [NumberField K] in

/- English proof (translation)
Simplify using `[oneBlockForms]`.
-/
theorem oneBlockForms_symm_apply {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (a : Fin (e + 1)) (j : Fin (r + 1)) :
    oneBlockForms om ((oneBlockIndex e r).symm (a, j)) = Pi.single j ((om a : 𝓞 K) : K) := by
  simp [oneBlockForms]

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[← linearIndependent_equiv (oneBlockIndex e r).symm]`. Establish `hψ : oneBlockForms (r` using `r) om ∘ (oneBlockIndex e r).symm = fun p : Fin (e + 1) × Fin (r + 1) ↦ (Pi.single p.2 ((om p.1 : 𝓞 K) : K) : Fin (r + 1) → K) := by`. Use function extensionality and compare the values at `p`. Conclude with `oneBlockForms_symm_apply om p.1 p.2`. Rewrite using `[hψ, Fintype.linearIndependent_iff]`.

Introduce and unpack `g hg ⟨a, j⟩`. Establish `hj` using `congrFun hg j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Fintype.sum_prod_type, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hj`. Establish `h2 : ∑ a', g (a', j) • om a' = 0`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Use `push_cast`. Simplify using `using hj`. Conclude with `Fintype.linearIndependent_iff.mp om.linearIndependent _ h2 a`.
-/
theorem oneBlockForms_linearIndependent {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    LinearIndependent ℤ (oneBlockForms (r := r) om) := by
  rw [← linearIndependent_equiv (oneBlockIndex e r).symm]
  have hψ : oneBlockForms (r := r) om ∘ (oneBlockIndex e r).symm =
      fun p : Fin (e + 1) × Fin (r + 1) ↦ (Pi.single p.2 ((om p.1 : 𝓞 K) : K) : Fin (r + 1) → K) := by
    funext p
    exact oneBlockForms_symm_apply om p.1 p.2
  rw [hψ, Fintype.linearIndependent_iff]
  rintro g hg ⟨a, j⟩
  have hj := congrFun hg j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Fintype.sum_prod_type, Pi.single_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hj
  have h2 : ∑ a', g (a', j) • om a' = 0 := by
    apply RingOfIntegers.coe_injective
    push_cast
    simpa using hj
  exact Fintype.linearIndependent_iff.mp om.linearIndependent _ h2 a

/- English proof (translation)
Introduce `K _ _ e r om`. Use `⟨⟨oneBlockForms_linearIndependent om, le_antisymm ?_ ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, rfl⟩ v hv`. Take `⟨b, hb⟩` from `standard_coord_integral hv (oneBlockIndex e r p).2`.

Use `⟨om (oneBlockIndex e r p).1 * b, ?_⟩` and prove the remaining obligations. Simplify using `only [oneBlockForms, single_dotProduct, map_mul, hb]`. Introduce `ψ hψ`. Establish `hj : ∀ j, ∃ b : 𝓞 K, ψ j = algebraMap (𝓞 K) K b`. Introduce `j`.

Take `⟨b, hb⟩` from `hψ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)`. Conclude with `⟨b, by rw [hb, dotProduct_single, mul_one]⟩`. Use `choose b hb using hj`. Establish `hsum : ψ = ∑ j, ∑ a, om.repr (b j) a • oneBlockForms (r` using `r) om ((oneBlockIndex e r).symm (a, j)) := by`. Use function extensionality and compare the values at `i`.

Simplify using `only [oneBlockForms_symm_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[hb i]`. Use `conv_lhs => rw [← om.sum_repr (b i)]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ fun j _ ↦ Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `hmap : latticeMap (oneBlockForms (r` using `r) om) = oneBlockMap om := by`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using `[latticeMap, oneBlockMap]`. Introduce `v`. Simplify using `only [latticeMap, oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms, latticeForm]`.

Rewrite using `[Finset.sum_eq_single (oneBlockIndex e r v.2).2]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[hi]`. Simplify using the standard rewrite rules.

Unfold `latticeIdeal oneBlockIdeal`. Rewrite using `[hmap]`. Introduce `σ w`. Use function extensionality and compare the values at `_ p`. Simplify using `only [latticePoint, oneBlockPoint, oneBlockForms]`.

Rewrite using `[Finset.sum_eq_single (oneBlockIndex e r p).2]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[hi]`. Simplify using the standard rewrite rules.
-/
theorem OneBlockStandard.proof : OneBlockStandard.Statement := by
  intro K _ _ e r om
  refine ⟨⟨oneBlockForms_linearIndependent om, le_antisymm ?_ ?_⟩, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩ v hv
    obtain ⟨b, hb⟩ := standard_coord_integral hv (oneBlockIndex e r p).2
    refine ⟨om (oneBlockIndex e r p).1 * b, ?_⟩
    simp only [oneBlockForms, single_dotProduct, map_mul, hb]
  · intro ψ hψ
    have hj : ∀ j, ∃ b : 𝓞 K, ψ j = algebraMap (𝓞 K) K b := by
      intro j
      obtain ⟨b, hb⟩ := hψ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨b, by rw [hb, dotProduct_single, mul_one]⟩
    choose b hb using hj
    have hsum : ψ = ∑ j, ∑ a, om.repr (b j) a •
        oneBlockForms (r := r) om ((oneBlockIndex e r).symm (a, j)) := by
      funext i
      simp only [oneBlockForms_symm_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
        smul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hb i]
      conv_lhs => rw [← om.sum_repr (b i)]
      push_cast
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.sum_mem _ fun a _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hmap : latticeMap (oneBlockForms (r := r) om) = oneBlockMap om := by
      apply MvPolynomial.ringHom_ext
      · intro n
        simp [latticeMap, oneBlockMap]
      · intro v
        simp only [latticeMap, oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms, latticeForm]
        rw [Finset.sum_eq_single (oneBlockIndex e r v.2).2]
        · simp
        · intro i _ hi
          simp [hi]
        · simp
    unfold latticeIdeal oneBlockIdeal
    rw [hmap]
  · intro σ w
    funext _ p
    simp only [latticePoint, oneBlockPoint, oneBlockForms]
    rw [Finset.sum_eq_single (oneBlockIndex e r p).2]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

end

end GroundTheory.Heights₂.Heights
