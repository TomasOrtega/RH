import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Introduce `p _ S _ _ ι _ _ Q N hN`. Use `set L : (ι → S) → (ι → S) := fun w => Q.mulVec fun k => frobenius S p (w k) with hL`. Set `F : AddMonoid.End (ι → S)` to `{ toFun := L map_zero' := by`. Simplify using `only [L, Pi.zero_apply, map_zero]`. Conclude with `Matrix.mulVec_zero Q`.

Use the proof step `map_add' := by`. Introduce `x y`. Simplify using `only [L, Pi.add_apply, map_add]`. Conclude with `Matrix.mulVec_add Q _ _ }`. Establish `hF : ∀ n, ⇑(F ^ n) = L^[n]` using `fun n => AddMonoid.End.coe_pow (M := ι → S) F n`.

Establish `hsmul : ∀ (a : S) (w : ι → S), L (a • w) = a ^ p • L w`. Introduce `a w`. Simplify using `only [L]`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`.

Use extensionality with `k`. Simplify using `[frobenius_def, mul_pow]`. Establish `hsmulN : ∀ n (a : S) (w : ι → S), L^[n] (a • w) = a ^ (p ^ n) • L^[n] w`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro a w`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `a w`. Rewrite using `[Function.iterate_succ_apply, hsmul, ih, ← pow_mul, ← pow_succ', Function.iterate_succ_apply]`.

Establish `hdecomp : ∀ w : ι → S, L^[N] w = ∑ j, (w j) ^ (p ^ N) • L^[N] (Pi.single j 1)`. Introduce `w`. Use `conv_lhs => rw [← Finset.univ_sum_single w]`. Rewrite using `[← hF, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hF, ← hsmulN]`. Use `congr 1`. Use extensionality with `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Set `J : Ideal S` to `Ideal.span (Set.range fun ji : ι × ι => L^[N] (Pi.single ji.1 1) ji.2)`. Establish `hJnil : IsNilpotent J`. Use `(Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range _))).2 ?_` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨⟨j, i⟩, rfl⟩`. Conclude with `(mem_nilradical).2 (hN j i)`. Establish `hstep : ∀ k (w : ι → S), (∀ i, w i ∈ J ^ k) → ∀ i, L^[N] w i ∈ J ^ (k + 1)`. Introduce `k w hw i`.

Rewrite using `[hdecomp w, Finset.sum_apply]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, pow_succ]`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_of_mem _ (hw j) _ (pow_pos (Fact.out : p.Prime).pos _)) (Ideal.subset_span ⟨(j, i), rfl⟩)`. Establish `hall : ∀ k (z : ι → S), ∀ i, L^[N * k] z i ∈ J ^ k`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z i`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `z i`. Rewrite using `[show N * (k + 1) = N + N * k by ring, Function.iterate_add_apply]`. Conclude with `hstep k _ (ih z) i`. Take `⟨m, hm⟩` from `hJnil`. Use `⟨N * m, fun z => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `h` using `hall m z i`. Rewrite `h` using `[hm, Ideal.zero_eq_bot, Ideal.mem_bot]`. Conclude with `h`.
-/
theorem frobSemilinear_iterate_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  intro p _ S _ _ ι _ _ Q N hN
  set L : (ι → S) → (ι → S) := fun w => Q.mulVec fun k => frobenius S p (w k) with hL
  let F : AddMonoid.End (ι → S) :=
    { toFun := L
      map_zero' := by
        simp only [L, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero Q
      map_add' := by
        intro x y
        simp only [L, Pi.add_apply, map_add]
        exact Matrix.mulVec_add Q _ _ }
  have hF : ∀ n, ⇑(F ^ n) = L^[n] := fun n => AddMonoid.End.coe_pow (M := ι → S) F n
  have hsmul : ∀ (a : S) (w : ι → S), L (a • w) = a ^ p • L w := by
    intro a w
    simp only [L]
    rw [← Matrix.mulVec_smul]
    congr 1
    ext k
    simp [frobenius_def, mul_pow]
  have hsmulN : ∀ n (a : S) (w : ι → S), L^[n] (a • w) = a ^ (p ^ n) • L^[n] w := by
    intro n
    induction n with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply, hsmul, ih, ← pow_mul, ← pow_succ', Function.iterate_succ_apply]
  have hdecomp : ∀ w : ι → S, L^[N] w = ∑ j, (w j) ^ (p ^ N) • L^[N] (Pi.single j 1) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, ← hsmulN]
    congr 1
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  let J : Ideal S := Ideal.span (Set.range fun ji : ι × ι => L^[N] (Pi.single ji.1 1) ji.2)
  have hJnil : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range _))).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact (mem_nilradical).2 (hN j i)
  have hstep : ∀ k (w : ι → S), (∀ i, w i ∈ J ^ k) → ∀ i, L^[N] w i ∈ J ^ (k + 1) := by
    intro k w hw i
    rw [hdecomp w, Finset.sum_apply]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, pow_succ]
    exact Ideal.mul_mem_mul
      (Ideal.pow_mem_of_mem _ (hw j) _ (pow_pos (Fact.out : p.Prime).pos _))
      (Ideal.subset_span ⟨(j, i), rfl⟩)
  have hall : ∀ k (z : ι → S), ∀ i, L^[N * k] z i ∈ J ^ k := by
    intro k
    induction k with
    | zero => intro z i; simp
    | succ k ih =>
      intro z i
      rw [show N * (k + 1) = N + N * k by ring, Function.iterate_add_apply]
      exact hstep k _ (ih z) i
  obtain ⟨m, hm⟩ := hJnil
  refine ⟨N * m, fun z => ?_⟩
  funext i
  have h := hall m z i
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

end GlobalTheory
