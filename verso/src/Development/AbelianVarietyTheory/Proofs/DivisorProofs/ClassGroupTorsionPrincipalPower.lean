import Mathlib

namespace GlobalTheory

open Submodule

/- English proof (translation)
Use `set Q := A ⧸ Ideal.span {(M : A)}`. Establish `hfin : Module.Finite ℤ Q` using `Module.Finite.of_surjective (Ideal.Quotient.mk (Ideal.span {(M : A)})).toAddMonoidHom.toIntLinearMap Ideal.Quotient.mk_surjective`. Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`. Use `⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Use `show M • Ideal.Quotient.mk _ a = 0`. Rewrite using `[zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(M : A)})), ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`.
-/
theorem finite_quot_span_intCast (A : Type) [CommRing A] [Module.Finite ℤ A] (M : ℤ) (hM : M ≠ 0) :
    Finite (A ⧸ Ideal.span {(M : A)}) := by
  set Q := A ⧸ Ideal.span {(M : A)}
  have hfin : Module.Finite ℤ Q :=
    Module.Finite.of_surjective (Ideal.Quotient.mk (Ideal.span {(M : A)})).toAddMonoidHom.toIntLinearMap
      Ideal.Quotient.mk_surjective
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  show M • Ideal.Quotient.mk _ a = 0
  rw [zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(M : A)})), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/- English proof (translation)
Use `haveI := finite_quot_span_intCast A M hM`. Set `f : Submodule A K → Set (A ⧸ Ideal.span {(M : A)})` to `fun N => Ideal.Quotient.mk _ '' (N.comap (Algebra.linearMap A K) : Set A)`. Establish `key : ∀ N₁ N₂ : Submodule A K, (M : K) ∈ N₂ → f N₁ = f N₂ → N₁.comap (Algebra.linearMap A K) ≤ N₂.comap (Algebra.linearMap A K)`. Introduce `N₁ N₂ h2 hf x hx`. Establish `: Ideal.Quotient.mk (Ideal.span {(M : A)}) x ∈ f N₂` using `hf ▸ ⟨x, hx, rfl⟩`.

Take `⟨y, hy, hxy⟩` from `this`. Rewrite `hxy` using `[Ideal.Quotient.eq]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hxy`. Establish `hM2 : ((M : A)) ∈ N₂.comap (Algebra.linearMap A K)`. Simplify using `[h2]`.

Establish `: x = y - c * (M : A)` using `by rw [hc]; ring`. Rewrite using `[this]`. Conclude with `sub_mem hy (Submodule.smul_mem _ c hM2)`. Use `Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce `N₁ h1 N₂ h2 hf`.

Establish `e : N₁.comap (Algebra.linearMap A K) = N₂.comap (Algebra.linearMap A K)` using `le_antisymm (key _ _ h2.2 hf) (key _ _ h1.2 hf.symm)`. Rewrite using `[← Submodule.map_comap_eq_self (f := Algebra.linearMap A K) (h1.1.trans (Submodule.one_eq_range).le), ← Submodule.map_comap_eq_self (f := Algebra.linearMap A K) (h2.1.trans (Submodule.one_eq_range).le), e]`.
-/
theorem finite_setOf_le_one_intCast_mem (A K : Type) [CommRing A] [Module.Finite ℤ A]
    [Field K] [Algebra A K] (M : ℤ) (hM : M ≠ 0) :
    {N : Submodule A K | N ≤ 1 ∧ (M : K) ∈ N}.Finite := by
  haveI := finite_quot_span_intCast A M hM
  let f : Submodule A K → Set (A ⧸ Ideal.span {(M : A)}) := fun N =>
    Ideal.Quotient.mk _ '' (N.comap (Algebra.linearMap A K) : Set A)
  have key : ∀ N₁ N₂ : Submodule A K, (M : K) ∈ N₂ → f N₁ = f N₂ →
      N₁.comap (Algebra.linearMap A K) ≤ N₂.comap (Algebra.linearMap A K) := by
    intro N₁ N₂ h2 hf x hx
    have : Ideal.Quotient.mk (Ideal.span {(M : A)}) x ∈ f N₂ := hf ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := this
    rw [Ideal.Quotient.eq] at hxy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxy
    have hM2 : ((M : A)) ∈ N₂.comap (Algebra.linearMap A K) := by
      simp [h2]
    have : x = y - c * (M : A) := by rw [hc]; ring
    rw [this]
    exact sub_mem hy (Submodule.smul_mem _ c hM2)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro N₁ h1 N₂ h2 hf
  have e : N₁.comap (Algebra.linearMap A K) = N₂.comap (Algebra.linearMap A K) :=
    le_antisymm (key _ _ h2.2 hf) (key _ _ h1.2 hf.symm)
  rw [← Submodule.map_comap_eq_self (f := Algebra.linearMap A K) (h1.1.trans (Submodule.one_eq_range).le),
    ← Submodule.map_comap_eq_self (f := Algebra.linearMap A K) (h2.1.trans (Submodule.one_eq_range).le), e]

/- English proof (translation)
Introduce `A K _ _ _ _ _ _ M hM H I J hIJ`. Establish `hpow : ∀ n : ℕ, I ^ n * J ^ n = 1` using `fun n => by rw [← mul_pow, hIJ, one_pow]`. Use `choose x hx0 hxle hxM using fun n : ℕ => H (I ^ n) (J ^ n) (hpow n)`. Establish `step : ∀ a c : ℕ, 0 < c → span A {x a} * I ^ a = span A {x (a + c)} * I ^ (a + c) → ∃ e : ℕ, 0 < e ∧ ∃ y : K, I ^ e = span A {y}`. Introduce `a c hc h`.

Establish `h1 : span A {x a} = span A {x (a + c)} * I ^ c`. Combine the equalities or inequalities in the displayed calculation. Use `⟨c, hc, (x (a + c))⁻¹ * x a, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ (hx0 _), ← one_eq_span, one_mul]`.

Use `_ = span A {(x (a + c))⁻¹} * span A {x a} := by rw [mul_assoc, h1]`. Use `_ = _ := by rw [span_mul_span, Set.singleton_mul_singleton]`. Use `haveI : Finite {N : Submodule A K | N ≤ 1 ∧ (M : K) ∈ N} := (finite_setOf_le_one_intCast_mem A K M hM).to_subtype`. Take `⟨a, b, hab, he⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨span A {x n} * I ^ n, hxle n, hxM n⟩ : {N : Submodule A K | N ≤ 1 ∧ (M : K) ∈ N}))`. Establish `he'` using `congrArg Subtype.val he`.

Simplify using `only at he'`. Break down `lt_or_gt_of_ne hab with hlt | hlt` into its components or cases. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_lt hlt`. Conclude with `step a (c + 1) (Nat.succ_pos c) (by rw [← add_assoc]; exact he')`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_lt hlt`.

Conclude with `step b (c + 1) (Nat.succ_pos c) (by rw [← add_assoc]; exact he'.symm)`.
-/
theorem exists_pow_eq_span_singleton_of_intCast_mem : ∀ (A K : Type) [CommRing A] [IsDomain A] [Module.Finite ℤ A]
    [Field K] [Algebra A K] [IsFractionRing A K] (M : ℤ), M ≠ 0 →
    (∀ I J : Submodule A K, I * J = 1 →
      ∃ x : K, x ≠ 0 ∧ Submodule.span A {x} * I ≤ 1 ∧ (M : K) ∈ Submodule.span A {x} * I) →
    ∀ I J : Submodule A K, I * J = 1 → ∃ e : ℕ, 0 < e ∧ ∃ x : K, I ^ e = Submodule.span A {x} := by
  intro A K _ _ _ _ _ _ M hM H I J hIJ
  have hpow : ∀ n : ℕ, I ^ n * J ^ n = 1 := fun n => by rw [← mul_pow, hIJ, one_pow]
  choose x hx0 hxle hxM using fun n : ℕ => H (I ^ n) (J ^ n) (hpow n)
  have step : ∀ a c : ℕ, 0 < c → span A {x a} * I ^ a = span A {x (a + c)} * I ^ (a + c) →
      ∃ e : ℕ, 0 < e ∧ ∃ y : K, I ^ e = span A {y} := by
    intro a c hc h
    have h1 : span A {x a} = span A {x (a + c)} * I ^ c :=
      calc span A {x a} = span A {x a} * I ^ a * J ^ a := by rw [mul_assoc, hpow, mul_one]
        _ = span A {x (a + c)} * I ^ (a + c) * J ^ a := by rw [h]
        _ = span A {x (a + c)} * I ^ c * (I ^ a * J ^ a) := by rw [pow_add]; ring
        _ = _ := by rw [hpow, mul_one]
    refine ⟨c, hc, (x (a + c))⁻¹ * x a, ?_⟩
    calc I ^ c = span A {(x (a + c))⁻¹} * span A {x (a + c)} * I ^ c := by
          rw [span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ (hx0 _), ← one_eq_span, one_mul]
      _ = span A {(x (a + c))⁻¹} * span A {x a} := by rw [mul_assoc, h1]
      _ = _ := by rw [span_mul_span, Set.singleton_mul_singleton]
  haveI : Finite {N : Submodule A K | N ≤ 1 ∧ (M : K) ∈ N} :=
    (finite_setOf_le_one_intCast_mem A K M hM).to_subtype
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨span A {x n} * I ^ n, hxle n, hxM n⟩ : {N : Submodule A K | N ≤ 1 ∧ (M : K) ∈ N}))
  have he' := congrArg Subtype.val he
  simp only at he'
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact step a (c + 1) (Nat.succ_pos c) (by rw [← add_assoc]; exact he')
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact step b (c + 1) (Nat.succ_pos c) (by rw [← add_assoc]; exact he'.symm)

end GlobalTheory
