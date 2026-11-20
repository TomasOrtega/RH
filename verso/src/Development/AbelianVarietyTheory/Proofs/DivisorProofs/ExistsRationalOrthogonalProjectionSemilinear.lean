import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `N hN x`. Use `⟨0, N.zero_mem, ?_⟩` and prove the remaining obligations.

Establish `hb : N = ⊥`. Rewrite using `[← Submodule.finrank_eq_zero]`. Use linear arithmetic over natural numbers and integers. Introduce `m hm`. Substitute `hb` using the available equality.

Rewrite `hm` using `[Submodule.mem_bot]`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `N hN x`.

Distinguish the cases in `h : ∃ v ∈ N, j v ≠ 0`. Take `⟨v, hvN, hv⟩` from `h`. Set `f : (Fin n → K) →ₛₗ[σ] ℂ` to `(innerₛₗ ℂ (j v)).comp j`. Establish `hf : ∀ z, f z = ⟪j v, j z⟫_ℂ` using `fun z => rfl`. Set `N'` to `N ⊓ LinearMap.ker f`.

Establish `hvv : ⟪j v, j v⟫_ℂ ≠ 0` using `inner_self_ne_zero.mpr hv`. Establish `hlt : N' < N`. Use `lt_of_le_of_ne inf_le_left ?_` and prove the remaining obligations. Introduce `heq`. Establish `hvN' : v ∈ N'` using `heq ▸ hvN`.

Establish `h2 : f v = 0` using `hvN'.2`. Rewrite `h2` using `[hf]`. Conclude with `hvv h2`. Establish `hN' : Module.finrank K N' ≤ d`. Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `hj v v`. Take `⟨b, hb⟩` from `hj v x`. Establish `hsa : σ a ≠ 0` using `by rw [ha]; exact hvv`. Take `⟨y', hy'N, hy'⟩` from `ih N' hN' (x - (b / a) • v)`.

Use `⟨(b / a) • v + y', N.add_mem (N.smul_mem _ hvN) (inf_le_left (a := N) hy'N), ?_⟩` and prove the remaining obligations. Establish `key : j x - j ((b / a) • v + y') = j (x - (b / a) • v) - j y'`. Simplify using `only [map_add, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`.

Establish `hy'k : ⟪j v, j y'⟫_ℂ = 0`. Establish `: f y' = 0` using `hy'N.2`. Rewrite `this` using `[hf]`. Then use the resulting hypothesis. Establish `hv0 : ⟪j v, j (x - (b / a) • v) - j y'⟫_ℂ = 0`. Rewrite using `[inner_sub_right, map_sub, inner_sub_right, hy'k, map_smulₛₗ, inner_smul_right, ← ha, ← hb, map_div₀, div_mul_cancel₀ _ hsa]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m hm`. Take `⟨e, he⟩` from `hj v m`. Establish `hm' : m - (e / a) • v ∈ N'`. Use `⟨N.sub_mem hm (N.smul_mem _ hvN), ?_⟩` and prove the remaining obligations.

Use `show f (m - (e / a) • v) = 0`. Rewrite using `[hf, map_sub, inner_sub_right, map_smulₛₗ, inner_smul_right, ← ha, ← he, map_div₀, div_mul_cancel₀ _ hsa, sub_self]`. Establish `hsplit : j m = σ (e / a) • j v + j (m - (e / a) • v)`. Rewrite using `[map_sub, map_smulₛₗ]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hsplit, inner_add_left, inner_smul_left, hv0, mul_zero, zero_add]`. Conclude with `hy' _ hm'`. Use `push_neg at h`. Use `⟨0, N.zero_mem, ?_⟩` and prove the remaining obligations. Introduce `m hm`.

Rewrite using `[h m hm, inner_zero_left]`.
-/
theorem exists_rational_orthogonal_projection_of_finrank_le (K : Type) [Field K] (σ : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W)
    (hj : ∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) :
    ∀ (d : ℕ) (N : Submodule K (Fin n → K)), Module.finrank K N ≤ d → ∀ (x : Fin n → K),
      ∃ y ∈ N, ∀ m ∈ N, ⟪j m, j x - j y⟫_ℂ = 0 := by
  intro d
  induction d with
  | zero =>
    intro N hN x
    refine ⟨0, N.zero_mem, ?_⟩
    have hb : N = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; omega
    intro m hm
    subst hb
    rw [Submodule.mem_bot] at hm
    subst hm
    simp
  | succ d ih =>
    intro N hN x
    by_cases h : ∃ v ∈ N, j v ≠ 0
    · obtain ⟨v, hvN, hv⟩ := h
      let f : (Fin n → K) →ₛₗ[σ] ℂ := (innerₛₗ ℂ (j v)).comp j
      have hf : ∀ z, f z = ⟪j v, j z⟫_ℂ := fun z => rfl
      let N' := N ⊓ LinearMap.ker f
      have hvv : ⟪j v, j v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
      have hlt : N' < N := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hvN' : v ∈ N' := heq ▸ hvN
        have h2 : f v = 0 := hvN'.2
        rw [hf] at h2
        exact hvv h2
      have hN' : Module.finrank K N' ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨a, ha⟩ := hj v v
      obtain ⟨b, hb⟩ := hj v x
      have hsa : σ a ≠ 0 := by rw [ha]; exact hvv
      obtain ⟨y', hy'N, hy'⟩ := ih N' hN' (x - (b / a) • v)
      refine ⟨(b / a) • v + y', N.add_mem (N.smul_mem _ hvN) (inf_le_left (a := N) hy'N), ?_⟩
      have key : j x - j ((b / a) • v + y') = j (x - (b / a) • v) - j y' := by
        simp only [map_add, map_sub]; abel
      rw [key]
      have hy'k : ⟪j v, j y'⟫_ℂ = 0 := by
        have : f y' = 0 := hy'N.2
        rwa [hf] at this
      have hv0 : ⟪j v, j (x - (b / a) • v) - j y'⟫_ℂ = 0 := by
        rw [inner_sub_right, map_sub, inner_sub_right, hy'k, map_smulₛₗ, inner_smul_right, ← ha, ← hb,
          map_div₀, div_mul_cancel₀ _ hsa]
        ring
      intro m hm
      obtain ⟨e, he⟩ := hj v m
      have hm' : m - (e / a) • v ∈ N' := by
        refine ⟨N.sub_mem hm (N.smul_mem _ hvN), ?_⟩
        show f (m - (e / a) • v) = 0
        rw [hf, map_sub, inner_sub_right, map_smulₛₗ, inner_smul_right, ← ha, ← he, map_div₀,
          div_mul_cancel₀ _ hsa, sub_self]
      have hsplit : j m = σ (e / a) • j v + j (m - (e / a) • v) := by
        rw [map_sub, map_smulₛₗ]; abel
      rw [hsplit, inner_add_left, inner_smul_left, hv0, mul_zero, zero_add]
      exact hy' _ hm'
    · push_neg at h
      refine ⟨0, N.zero_mem, ?_⟩
      intro m hm
      rw [h m hm, inner_zero_left]

/- English proof (translation)
Introduce `K _ σ W _ _ _ n j hj N x`. Take `⟨y, hyN, hy⟩` from `exists_rational_orthogonal_projection_of_finrank_le K σ W n j hj _ N le_rfl x`. Use `⟨y, hyN, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨m, hm, rfl⟩` from `hu`. Conclude with `hy m hm`. Consider the case `zero => exact inner_zero_left _`.

Consider the case `add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]`. Consider the case `smul c u _ hu => rw [inner_smul_left, hu, mul_zero]`.
-/
theorem exists_mem_sub_mem_orthogonal_span_of_inner_mem_range : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  intro K _ σ W _ _ _ n j hj N x
  obtain ⟨y, hyN, hy⟩ := exists_rational_orthogonal_projection_of_finrank_le K σ W n j hj _ N le_rfl x
  refine ⟨y, hyN, ?_⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨m, hm, rfl⟩ := hu
    exact hy m hm
  | zero => exact inner_zero_left _
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]

end GlobalTheory
