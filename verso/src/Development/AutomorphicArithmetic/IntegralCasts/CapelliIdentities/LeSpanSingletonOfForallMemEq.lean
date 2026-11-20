import Mathlib

/- English proof (translation)
Introduce `R _ π ξ hc J h x hx`. Use `choose! a z hz he using h`. Establish `hsm : ∀ (n : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ u - v`. Introduce `n u v`. Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]`.

Establish `hzs : ∀ n : ℕ, z^[n] x ∈ J`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact hx`. Consider the case `succ n ih => rw [Function.iterate_succ_apply']`.

Conclude with `hz _ ih`. Set `f : ℕ → R` to `fun n => ∑ i ∈ Finset.range n, a (z^[i] x) * π ^ i`. Establish `hf : ∀ n, f (n + 1) = f n + a (z^[n] x) * π ^ n` using `fun n => Finset.sum_range_succ _ _`. Establish `key : ∀ n, x = f n * ξ + z^[n] x * π ^ n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp [f]`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', hf]`. Establish `h1` using `he _ (hzs n)`.

Take the linear combination `ih + π ^ n * h1`. Establish `hcau : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R R)]`. Introduce `m n hmn`. Rewrite using `[hsm]`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[hf, ← sub_sub]`. Conclude with `dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow π hmn) _)`. Take `⟨L, hL⟩` from `IsPrecomplete.prec hc.toIsPrecomplete hcau`.

Establish `h0 : x - L * ξ = 0`. Apply `IsHausdorff.haus hc.toIsHausdorff` to reduce the goal to its premises. Introduce `n`. Rewrite using `[hsm]`. Take `⟨c, hc'⟩` from `(hsm _ _ _).1 (hL n)`.

Conclude with `⟨c * ξ + z^[n] x, by linear_combination key n + ξ * hc'⟩`. Conclude with `Ideal.mem_span_singleton'.2 ⟨L, (sub_eq_zero.1 h0).symm⟩`.
-/
theorem UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π ξ : R} [IsAdicComplete (Ideal.span {π}) R] {J : Ideal R},
      (∀ x ∈ J, ∃ (a : R), ∃ z ∈ J, x = a * ξ + z * π) → J ≤ Ideal.span {ξ} := by
  intro R _ π ξ hc J h x hx
  choose! a z hz he using h
  have hsm : ∀ (n : ℕ) (u v : R),
      u ≡ v [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton]
  have hzs : ∀ n : ℕ, z^[n] x ∈ J := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hz _ ih
  let f : ℕ → R := fun n => ∑ i ∈ Finset.range n, a (z^[i] x) * π ^ i
  have hf : ∀ n, f (n + 1) = f n + a (z^[n] x) * π ^ n := fun n => Finset.sum_range_succ _ _
  have key : ∀ n, x = f n * ξ + z^[n] x * π ^ n := by
    intro n
    induction n with
    | zero => simp [f]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf]
      have h1 := he _ (hzs n)
      linear_combination ih + π ^ n * h1
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hf, ← sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow π hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcau
  have h0 : x - L * ξ = 0 := by
    apply IsHausdorff.haus hc.toIsHausdorff
    intro n
    rw [hsm]
    obtain ⟨c, hc'⟩ := (hsm _ _ _).1 (hL n)
    exact ⟨c * ξ + z^[n] x, by linear_combination key n + ξ * hc'⟩
  exact Ideal.mem_span_singleton'.2 ⟨L, (sub_eq_zero.1 h0).symm⟩
