import Mathlib

namespace GroundTheory.Variant₂.N1

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem mem_span_singleton_pow_smul_top_iff {A : Type*} [CommRing A] (a x : A) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Take `⟨L, hL⟩` from `(inferInstance : IsPrecomplete (Ideal.span {a}) A).prec' (fun n => ∑ k ∈ Finset.range n, a ^ k * b k) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left, dvd_neg]`. Use `Finset.dvd_sum fun k hk => ?_` and prove the remaining obligations. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow a (Finset.mem_Ico.1 hk).1) _)`.

Conclude with `⟨L, fun n => (mem_span_singleton_pow_smul_top_iff a _ n).1 ((SModEq.sub_mem).1 (hL n))⟩`.
-/
theorem exists_limit_sum_pow_mul {A : Type*} [CommRing A] {a : A}
    [IsPrecomplete (Ideal.span {a}) A] (b : ℕ → A) :
    ∃ L : A, ∀ n : ℕ, a ^ n ∣ (∑ k ∈ Finset.range n, a ^ k * b k) - L := by
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (Ideal.span {a}) A).prec'
    (fun n => ∑ k ∈ Finset.range n, a ^ k * b k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff,
        ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow a (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun n => (mem_span_singleton_pow_smul_top_iff a _ n).1 ((SModEq.sub_mem).1 (hL n))⟩

/- English proof (translation)
Introduce `hfa X ψ h`. Use `choose b s nx hstep using h`. Introduce `y`. Take `⟨B, hB⟩` from `exists_limit_sum_pow_mul (a := a) (fun k => b (nx^[k] y))`. Take `⟨S, hS⟩` from `exists_limit_sum_pow_mul (a := r) (fun k => s (nx^[k] y))`.

Use `⟨B, S, ?_⟩` and prove the remaining obligations. Establish `key : ∀ n : ℕ, ψ y = f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) + X * (∑ k ∈ Finset.range n, r ^ k * s (nx^[k] y)) + r ^ n * ψ (nx^[n] y)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Establish `h1` using `hstep (nx^[n] y)`. Rewrite using `[Function.iterate_succ_apply', Finset.sum_range_succ, Finset.sum_range_succ]`. Simplify using `only [map_add, map_mul, map_pow, hfa] at ih ⊢`. Take the linear combination `ih + r ^ n * h1`.

Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := Ideal.span {r}) _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff]`. Take `⟨c, hc⟩` from `hB n`. Take `⟨d, hd⟩` from `hS n`.

Establish `hfB : f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) = f B + r ^ n * f c`. Rewrite using `[← hfa, ← map_pow, ← map_mul, ← map_add]`. Use `congr 1`. Take the linear combination `hc`. Conclude with `⟨f c + X * d + ψ (nx^[n] y), by linear_combination key n + hfB + X * hd⟩`.
-/
theorem exists_eq_add_mul_of_forall' {A : Type*} {R : Type*} {ι : Type*} [CommRing A]
    [CommRing R] {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) :
    f a = r →
      ∀ (X : R) (ψ : ι → R),
        (∀ (y : ι), ∃ (b : A) (s : R) (y' : ι), ψ y = f b + X * s + r * ψ y') →
          ∀ (y : ι), ∃ (b : A) (s : R), ψ y = f b + X * s := by
  intro hfa X ψ h
  choose b s nx hstep using h
  intro y
  obtain ⟨B, hB⟩ := exists_limit_sum_pow_mul (a := a) (fun k => b (nx^[k] y))
  obtain ⟨S, hS⟩ := exists_limit_sum_pow_mul (a := r) (fun k => s (nx^[k] y))
  refine ⟨B, S, ?_⟩
  have key : ∀ n : ℕ, ψ y = f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) +
      X * (∑ k ∈ Finset.range n, r ^ k * s (nx^[k] y)) + r ^ n * ψ (nx^[n] y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep (nx^[n] y)
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [map_add, map_mul, map_pow, hfa] at ih ⊢
      linear_combination ih + r ^ n * h1
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {r}) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff]
  obtain ⟨c, hc⟩ := hB n
  obtain ⟨d, hd⟩ := hS n
  have hfB : f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) = f B + r ^ n * f c := by
    rw [← hfa, ← map_pow, ← map_mul, ← map_add]
    congr 1
    linear_combination hc
  exact ⟨f c + X * d + ψ (nx^[n] y), by linear_combination key n + hfB + X * hd⟩

end GroundTheory.Variant₂.N1
