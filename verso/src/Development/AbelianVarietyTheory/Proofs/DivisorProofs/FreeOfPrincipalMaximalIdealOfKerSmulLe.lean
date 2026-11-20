import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ _ x hx N _ _ hfin hann`. Use `haveI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N`. Apply `Module.free_of_maximalIdeal_rTensor_injective` to reduce the goal to its premises. Establish `hxm : x ∈ IsLocalRing.maximalIdeal R` using `hx ▸ Ideal.subset_span rfl`. Set `X : IsLocalRing.maximalIdeal R` to `⟨x, hxm⟩`.

Establish `hrep : ∀ t : (IsLocalRing.maximalIdeal R) ⊗[R] N, ∃ n : N, t = X ⊗ₜ n`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul m n`.

Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r, r * x = (m : R) := by`. Establish `hm : (m : R) ∈ Ideal.span {x}` using `hx ▸ m.2`. Rewrite `hm` using `[Ideal.mem_span_singleton']`. Then use the resulting hypothesis. Use `⟨r • n, ?_⟩` and prove the remaining obligations. Rewrite using `[← TensorProduct.smul_tmul]`.

Use `congr 1`. Use `ext`. Simplify using `[X, hr]`. Consider the case `add a b ha hb`. Take `⟨n1, rfl⟩` from `ha`.

Take `⟨n2, rfl⟩` from `hb`. Conclude with `⟨n1 + n2, by rw [TensorProduct.tmul_add]⟩`. Establish `hspan : ∀ a ∈ Ideal.span {a : R | x * a = 0}, x * a = 0`. Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem y hy => exact hy`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]`. Consider the case `smul c y _ hy => rw [smul_eq_mul, mul_left_comm, hy, mul_zero]`. Establish `hzero : ∀ n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N), (X ⊗ₜ[R] n : (IsLocalRing.maximalIdeal R) ⊗[R] N) = 0`.

Introduce `n hn`. Use `Submodule.smul_induction_on hn ?_ ?_` and prove the remaining obligations. Introduce `a ha m _`. Rewrite using `[← TensorProduct.smul_tmul]`. Establish `: a • X = 0` using `by ext; simp [X, mul_comm a x, hspan a ha]`.

Rewrite using `[this, TensorProduct.zero_tmul]`. Introduce `m1 m2 h1 h2`. Rewrite using `[TensorProduct.tmul_add, h1, h2, add_zero]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`.

Take `⟨n, rfl⟩` from `hrep t`. Establish `hxn : x • n = 0`. Establish `h2` using `congrArg (TensorProduct.lid R N) ht`. Simplify `h2` using `[X]`. Conclude with `hzero n (hann n hxn)`.
-/
theorem free_of_principal_maximalIdeal_of_ker_smul_le :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      IsLocalRing.maximalIdeal R = Ideal.span {x} →
      ∀ (N : Type 1) [AddCommGroup N] [Module R N], Module.Finite R N →
        (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N)) →
        Module.Free R N := by
  intro R _ _ _ x hx N _ _ hfin hann
  haveI : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  apply Module.free_of_maximalIdeal_rTensor_injective
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hx ▸ Ideal.subset_span rfl
  let X : IsLocalRing.maximalIdeal R := ⟨x, hxm⟩
  have hrep : ∀ t : (IsLocalRing.maximalIdeal R) ⊗[R] N, ∃ n : N, t = X ⊗ₜ n := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m n =>
      obtain ⟨r, hr⟩ : ∃ r, r * x = (m : R) := by
        have hm : (m : R) ∈ Ideal.span {x} := hx ▸ m.2
        rwa [Ideal.mem_span_singleton'] at hm
      refine ⟨r • n, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1; ext; simp [X, hr]
    | add a b ha hb =>
      obtain ⟨n1, rfl⟩ := ha; obtain ⟨n2, rfl⟩ := hb
      exact ⟨n1 + n2, by rw [TensorProduct.tmul_add]⟩
  have hspan : ∀ a ∈ Ideal.span {a : R | x * a = 0}, x * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_eq_mul, mul_left_comm, hy, mul_zero]
  have hzero : ∀ n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N),
      (X ⊗ₜ[R] n : (IsLocalRing.maximalIdeal R) ⊗[R] N) = 0 := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro a ha m _
      rw [← TensorProduct.smul_tmul]
      have : a • X = 0 := by ext; simp [X, mul_comm a x, hspan a ha]
      rw [this, TensorProduct.zero_tmul]
    · intro m1 m2 h1 h2
      rw [TensorProduct.tmul_add, h1, h2, add_zero]
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨n, rfl⟩ := hrep t
  have hxn : x • n = 0 := by
    have h2 := congrArg (TensorProduct.lid R N) ht
    simpa [X] using h2
  exact hzero n (hann n hxn)

end GlobalTheory
