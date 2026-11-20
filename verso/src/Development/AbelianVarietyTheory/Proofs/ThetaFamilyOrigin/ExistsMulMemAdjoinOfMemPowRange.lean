import Mathlib

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

open scoped Pointwise

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `t ht`. Rewrite `ht` using `[pow_zero, Set.mem_one]`.

Substitute `ht` using the available equality. Conclude with `SetLike.one_mem_graded 𝒜`. Consider the case `succ k ih`. Introduce `t ht`. Rewrite `ht` using `[pow_succ]`.

Take `⟨a, ha, b, ⟨i, rfl⟩, rfl⟩` from `ht`. Conclude with `SetLike.mul_mem_graded (ih a ha) (hx i)`.
-/
theorem mem_graded_of_mem_pow_range {K T : Type} [Field K] [CommRing T] [Algebra K T]
    (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] {m : ℕ} (x : Fin m → T) (hx : ∀ i, x i ∈ 𝒜 1) :
    ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, t ∈ 𝒜 k := by
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [pow_zero, Set.mem_one] at ht
    subst ht
    exact SetLike.one_mem_graded 𝒜
  | succ k ih =>
    intro t ht
    rw [pow_succ] at ht
    obtain ⟨a, ha, b, ⟨i, rfl⟩, rfl⟩ := ht
    exact SetLike.mul_mem_graded (ih a ha) (hx i)

/- English proof (translation)
Establish `h1 : ∀ u ∈ Submonoid.closure (Set.range x), ∃ j : ℕ, u ∈ (Set.range x) ^ j`. Introduce `u hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem y hy => exact ⟨1, by simpa using hy⟩`. Consider the case `one => exact ⟨0, by simp⟩`.

Consider the case `mul a b _ _ ha hb`. Take `⟨i, hi⟩` from `ha`. Take `⟨j, hj⟩` from `hb`. Conclude with `⟨i + j, by rw [pow_add]; exact Set.mul_mem_mul hi hj⟩`. Establish `h2 : ∀ u ∈ Submodule.span K (Submonoid.closure (Set.range x) : Set T), GradedAlgebra.proj 𝒜 k u ∈ Submodule.span K ((Set.range x) ^ k)`.

Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, hj⟩` from `h1 y hy`. Establish `hyj` using `mem_graded_of_mem_pow_range 𝒜 x hx j y hj`.

Rewrite using `[GradedAlgebra.proj_apply]`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Rewrite using `[DirectSum.decompose_of_mem_same 𝒜 hyj]`. Conclude with `Submodule.subset_span hj`.

Rewrite using `[DirectSum.decompose_of_mem_ne 𝒜 hyj hjk]`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c ha`. Establish `h3 : t ∈ Submodule.span K (Submonoid.closure (Set.range x) : Set T)`. Rewrite using `[← Algebra.adjoin_eq_span]`.

Conclude with `ht`. Establish `h4` using `h2 t h3`. Rewrite `h4` using `[GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 htk]`. Then use the resulting hypothesis.
-/
theorem mem_span_pow_range_of_mem_adjoin {K T : Type} [Field K] [CommRing T] [Algebra K T]
    (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] {m : ℕ} (x : Fin m → T) (hx : ∀ i, x i ∈ 𝒜 1)
    (k : ℕ) (t : T) (ht : t ∈ Algebra.adjoin K (Set.range x)) (htk : t ∈ 𝒜 k) :
    t ∈ Submodule.span K ((Set.range x) ^ k) := by
  have h1 : ∀ u ∈ Submonoid.closure (Set.range x), ∃ j : ℕ, u ∈ (Set.range x) ^ j := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem y hy => exact ⟨1, by simpa using hy⟩
    | one => exact ⟨0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      exact ⟨i + j, by rw [pow_add]; exact Set.mul_mem_mul hi hj⟩
  have h2 : ∀ u ∈ Submodule.span K (Submonoid.closure (Set.range x) : Set T),
      GradedAlgebra.proj 𝒜 k u ∈ Submodule.span K ((Set.range x) ^ k) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj⟩ := h1 y hy
      have hyj := mem_graded_of_mem_pow_range 𝒜 x hx j y hj
      rw [GradedAlgebra.proj_apply]
      by_cases hjk : j = k
      · subst hjk
        rw [DirectSum.decompose_of_mem_same 𝒜 hyj]
        exact Submodule.subset_span hj
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hyj hjk]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h3 : t ∈ Submodule.span K (Submonoid.closure (Set.range x) : Set T) := by
    rw [← Algebra.adjoin_eq_span]; exact ht
  have h4 := h2 t h3
  rwa [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 htk] at h4

/- English proof (translation)
Use `set S := Algebra.adjoin K (Set.range x) with hS`. Set `x' : Fin m → S` to `fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩`. Set `C : Ideal S` to `{ carrier := {a | s * (a : T) ∈ S} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, Subalgebra.coe_add, mul_add] at *`. Conclude with `S.add_mem ha hb`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul] at *`. Rewrite using `[mul_left_comm]`. Conclude with `S.mul_mem c.2 ha }`.

Establish `hle : Ideal.span (Set.range x') ≤ C.radical`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨n, hn⟩` from `hs i`. Conclude with `⟨n, hn⟩`.

Take `⟨N, hN⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hle (Submodule.fg_span (Set.finite_range x'))`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `key : ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, ∃ a ∈ Ideal.span (Set.range x') ^ k, (a : T) = t`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `t ht`. Rewrite `ht` using `[pow_zero, Set.mem_one]`. Substitute `ht` using the available equality. Conclude with `⟨1, by simp, rfl⟩`.

Consider the case `succ k ih`. Introduce `t ht`. Rewrite `ht` using `[pow_succ]`. Take `⟨a, ha, b, ⟨i, rfl⟩, rfl⟩` from `ht`. Take `⟨a', ha', rfl⟩` from `ih a ha`.

Use `⟨a' * x' i, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul ha' (Ideal.subset_span ⟨i, rfl⟩)`. Introduce `t ht`. Take `⟨a, ha, rfl⟩` from `key N t ht`.

Conclude with `hN ha`.
-/
theorem exists_mul_mem_adjoin_of_mem_pow_range {K T : Type} [Field K] [CommRing T] [Algebra K T]
    {m : ℕ} (x : Fin m → T) (s : T)
    (hs : ∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) :
    ∃ N : ℕ, ∀ t ∈ (Set.range x) ^ N, s * t ∈ Algebra.adjoin K (Set.range x) := by
  set S := Algebra.adjoin K (Set.range x) with hS
  let x' : Fin m → S := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let C : Ideal S :=
    { carrier := {a | s * (a : T) ∈ S}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, mul_add] at *
        exact S.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul] at *
        rw [mul_left_comm]
        exact S.mul_mem c.2 ha }
  have hle : Ideal.span (Set.range x') ≤ C.radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hs i
    exact ⟨n, hn⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Submodule.fg_span (Set.finite_range x'))
  refine ⟨N, ?_⟩
  have key : ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k,
      ∃ a ∈ Ideal.span (Set.range x') ^ k, (a : T) = t := by
    intro k
    induction k with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      subst ht
      exact ⟨1, by simp, rfl⟩
    | succ k ih =>
      intro t ht
      rw [pow_succ] at ht
      obtain ⟨a, ha, b, ⟨i, rfl⟩, rfl⟩ := ht
      obtain ⟨a', ha', rfl⟩ := ih a ha
      refine ⟨a' * x' i, ?_, rfl⟩
      rw [pow_succ]
      exact Ideal.mul_mem_mul ha' (Ideal.subset_span ⟨i, rfl⟩)
  intro t ht
  obtain ⟨a, ha, rfl⟩ := key N t ht
  exact hN ha

/- English proof (translation)
Introduce `K T _ _ _ _ 𝒜 _ m x hx hne d s hsd hs`. Take `⟨N, hN⟩` from `exists_mul_mem_adjoin_of_mem_pow_range x s hs`. Use `set S := Algebra.adjoin K (Set.range x) with hS`. Establish `hP : ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, t ∈ S`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `t ht`. Rewrite `ht` using `[pow_zero, Set.mem_one]`. Substitute `ht` using the available equality.

Conclude with `S.one_mem`. Consider the case `succ k ih`. Introduce `t ht`. Rewrite `ht` using `[pow_succ]`. Take `⟨a, ha, b, hb, rfl⟩` from `ht`.

Conclude with `S.mul_mem (ih a ha) (Algebra.subset_adjoin hb)`. Establish `hfin : ∀ k : ℕ, ((Set.range x) ^ k).Finite`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`.

Conclude with `Set.finite_one`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `ih.mul (Set.finite_range x)`. Use `isIntegral_of_smul_mem_submodule (Submodule.span S ((Set.range x) ^ N)) ?_ (Submodule.fg_span (hfin N)) s ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hne`.

Rewrite using `[Submodule.ne_bot_iff]`. Conclude with `⟨x i ^ N, Submodule.subset_span (Set.pow_mem_pow ⟨i, rfl⟩), pow_ne_zero N hi⟩`. Introduce `t ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem y hy`.

Establish `h1` using `mem_span_pow_range_of_mem_adjoin 𝒜 x hx (d + N) (s * y) (hN y hy) (SetLike.mul_mem_graded hsd (mem_graded_of_mem_pow_range 𝒜 x hx N y hy))`. Establish `h2 : Submodule.span K ((Set.range x) ^ (d + N)) ≤ (Submodule.span S ((Set.range x) ^ N)).restrictScalars K`. Rewrite using `[Submodule.span_le, pow_add]`. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Conclude with `Submodule.smul_mem (Submodule.span S ((Set.range x) ^ N)) (⟨a, hP d a ha⟩ : S) (Submodule.subset_span hb)`.

Conclude with `h2 h1`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul c a _ ha => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem isIntegral_adjoin_of_mul_pow_mem :
    (∀ (K T : Type) [Field K] [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s) := by
  intro K T _ _ _ _ 𝒜 _ m x hx hne d s hsd hs
  obtain ⟨N, hN⟩ := exists_mul_mem_adjoin_of_mem_pow_range x s hs
  set S := Algebra.adjoin K (Set.range x) with hS
  have hP : ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, t ∈ S := by
    intro k
    induction k with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      subst ht
      exact S.one_mem
    | succ k ih =>
      intro t ht
      rw [pow_succ] at ht
      obtain ⟨a, ha, b, hb, rfl⟩ := ht
      exact S.mul_mem (ih a ha) (Algebra.subset_adjoin hb)
  have hfin : ∀ k : ℕ, ((Set.range x) ^ k).Finite := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact Set.finite_one
    | succ k ih => rw [pow_succ]; exact ih.mul (Set.finite_range x)
  refine isIntegral_of_smul_mem_submodule (Submodule.span S ((Set.range x) ^ N)) ?_
    (Submodule.fg_span (hfin N)) s ?_
  · obtain ⟨i, hi⟩ := hne
    rw [Submodule.ne_bot_iff]
    exact ⟨x i ^ N, Submodule.subset_span (Set.pow_mem_pow ⟨i, rfl⟩), pow_ne_zero N hi⟩
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem y hy =>
      have h1 := mem_span_pow_range_of_mem_adjoin 𝒜 x hx (d + N) (s * y) (hN y hy)
        (SetLike.mul_mem_graded hsd (mem_graded_of_mem_pow_range 𝒜 x hx N y hy))
      have h2 : Submodule.span K ((Set.range x) ^ (d + N)) ≤
          (Submodule.span S ((Set.range x) ^ N)).restrictScalars K := by
        rw [Submodule.span_le, pow_add]
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact Submodule.smul_mem (Submodule.span S ((Set.range x) ^ N)) (⟨a, hP d a ha⟩ : S)
          (Submodule.subset_span hb)
      exact h2 h1
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

end GlobalTheory
