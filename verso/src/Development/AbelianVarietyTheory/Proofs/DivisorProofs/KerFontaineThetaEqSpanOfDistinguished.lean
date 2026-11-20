import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Set `g : {z // P z} → A × {z // P z}` to `fun z => ((h z.1 z.2).choose, ⟨(h z.1 z.2).choose_spec.choose, (h z.1 z.2).choose_spec.choose_spec.2⟩)`. Establish `hg : ∀ z : {z // P z}, z.1 = a * (g z).1 + q * (g z).2.1` using `fun z => (h z.1 z.2).choose_spec.choose_spec.1`. Set `xs : ℕ → {z // P z}` to `fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (g z).2) n`. Establish `hxs : ∀ n, xs (n + 1) = (g (xs n)).2` using `fun n => rfl`. Set `S : ℕ → A` to `fun n => ∑ k ∈ Finset.range n, q ^ k * (g (xs k)).1`.

Establish `hS : ∀ n, S (n + 1) = S n + q ^ n * (g (xs n)).1` using `fun n => Finset.sum_range_succ _ _`. Establish `hY : ∀ n, x = a * S n + q ^ n * (xs n).1`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [S, xs]`.

Consider the case `succ n ih`. Rewrite using `[hS, hxs]`. Take the linear combination `ih + q ^ n * hg (xs n)`. Establish `hC : ∀ m n, m ≤ n → S n - S m ∈ span {q ^ m}`. Introduce `m n hmn`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[hS, show S n + q ^ n * (g (xs n)).1 - S m = (S n - S m) + q ^ n * (g (xs n)).1 by ring]`. Use `add_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow q hmn) _))` and prove the remaining obligations.

Take `⟨L, hL⟩` from `(inferInstance : IsPrecomplete (span {q}) A).prec' S (by`. Introduce `m n hmn`. Simplify using `only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem (hC m n hmn))`.

Establish `hxL : x - a * L = 0`. Use `(inferInstance : IsHausdorff (span {q}) A).haus' _ (fun n => ?_)` and prove the remaining obligations. Establish `hn` using `hL n`. Simplify using `only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn ⊢`. Rewrite using `[sub_zero, show x - a * L = a * (S n - L) + q ^ n * (xs n).1 by`.

Take the linear combination `hY n]`. Conclude with `add_mem (mul_mem_left _ _ hn) (mul_mem_right _ _ (mem_span_singleton_self _))`. Conclude with `mem_span_singleton'.2 ⟨L, by rw [mul_comm]; exact (sub_eq_zero.1 hxL).symm⟩`.
-/
theorem mem_span_of_step_adic {A : Type*} [CommRing A] (q a : A)
    [IsAdicComplete (span {q}) A] (P : A → Prop)
    (h : ∀ x, P x → ∃ y x', x = a * y + q * x' ∧ P x') (x : A) (hx : P x) :
    x ∈ span {a} := by
  classical
  let g : {z // P z} → A × {z // P z} := fun z =>
    ((h z.1 z.2).choose, ⟨(h z.1 z.2).choose_spec.choose, (h z.1 z.2).choose_spec.choose_spec.2⟩)
  have hg : ∀ z : {z // P z}, z.1 = a * (g z).1 + q * (g z).2.1 := fun z =>
    (h z.1 z.2).choose_spec.choose_spec.1
  let xs : ℕ → {z // P z} := fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (g z).2) n
  have hxs : ∀ n, xs (n + 1) = (g (xs n)).2 := fun n => rfl
  let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, q ^ k * (g (xs k)).1
  have hS : ∀ n, S (n + 1) = S n + q ^ n * (g (xs n)).1 := fun n => Finset.sum_range_succ _ _
  have hY : ∀ n, x = a * S n + q ^ n * (xs n).1 := by
    intro n
    induction n with
    | zero => simp [S, xs]
    | succ n ih =>
      rw [hS, hxs]
      linear_combination ih + q ^ n * hg (xs n)
  have hC : ∀ m n, m ≤ n → S n - S m ∈ span {q ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hS, show S n + q ^ n * (g (xs n)).1 - S m = (S n - S m) + q ^ n * (g (xs n)).1 by ring]
      refine add_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow q hmn) _))
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (span {q}) A).prec' S (by
    intro m n hmn
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← neg_sub]
    exact neg_mem (hC m n hmn))
  have hxL : x - a * L = 0 := by
    refine (inferInstance : IsHausdorff (span {q}) A).haus' _ (fun n => ?_)
    have hn := hL n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn ⊢
    rw [sub_zero, show x - a * L = a * (S n - L) + q ^ n * (xs n).1 by
      linear_combination hY n]
    exact add_mem (mul_mem_left _ _ hn) (mul_mem_right _ _ (mem_span_singleton_self _))
  exact mem_span_singleton'.2 ⟨L, by rw [mul_comm]; exact (sub_eq_zero.1 hxL).symm⟩

/- English proof (translation)
Introduce `p _ R _ _ _ hreg ξ hθξ hdiv`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite `hx` using `[RingHom.mem_ker]`.

Use `mem_span_of_step_adic (p : WittVector p (PreTilt R p)) ξ (fun x => fontaineTheta R p x = 0) ?_ x hx` and prove the remaining obligations. Introduce `x hx`. Establish `hc : PreTilt.coeff 0 (x.coeff 0) = 0`. Rewrite using `[← mk_fontaineTheta, hx, map_zero]`. Take `⟨d, hd⟩` from `hdiv _ hc`.

Establish `hm : x - ξ * teichmuller p d ∈ span {(p : WittVector p (PreTilt R p))}`. Rewrite using `[← ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul]`. Express the relevant statement in the definitionally equal form `x.coeff 0 - constantCoeff ξ * (teichmuller p d).coeff 0 = 0`. Rewrite using `[teichmuller_coeff_zero, ← hd, sub_self]`. Take `⟨z, hz⟩` from `mem_span_singleton'.1 hm`.

Use `⟨teichmuller p d, z, by linear_combination -hz, ?_⟩` and prove the remaining obligations. Apply `hreg` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(p : R) * fontaineTheta R p z = (p : R) * 0`. Rewrite using `[mul_zero, ← map_natCast (fontaineTheta R p) p, ← map_mul, mul_comm, hz, map_sub, map_mul, hx, hθξ, zero_mul, sub_zero]`. Introduce `hx`.

Take `⟨a, rfl⟩` from `mem_span_singleton'.1 hx`. Rewrite using `[RingHom.mem_ker, map_mul, hθξ, mul_zero]`.
-/
theorem ker_fontaineTheta_eq_span_of_dvd : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) →
    ∀ ξ : WittVector p (PreTilt R p), fontaineTheta R p ξ = 0 →
    (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff ξ ∣ c) →
    RingHom.ker (fontaineTheta R p) = Ideal.span {ξ} := by
  intro p _ R _ _ _ hreg ξ hθξ hdiv
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    refine mem_span_of_step_adic (p : WittVector p (PreTilt R p)) ξ
      (fun x => fontaineTheta R p x = 0) ?_ x hx
    intro x hx
    have hc : PreTilt.coeff 0 (x.coeff 0) = 0 := by
      rw [← mk_fontaineTheta, hx, map_zero]
    obtain ⟨d, hd⟩ := hdiv _ hc
    have hm : x - ξ * teichmuller p d ∈ span {(p : WittVector p (PreTilt R p))} := by
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul]
      change x.coeff 0 - constantCoeff ξ * (teichmuller p d).coeff 0 = 0
      rw [teichmuller_coeff_zero, ← hd, sub_self]
    obtain ⟨z, hz⟩ := mem_span_singleton'.1 hm
    refine ⟨teichmuller p d, z, by linear_combination -hz, ?_⟩
    apply hreg
    change (p : R) * fontaineTheta R p z = (p : R) * 0
    rw [mul_zero, ← map_natCast (fontaineTheta R p) p, ← map_mul, mul_comm, hz, map_sub, map_mul,
      hx, hθξ, zero_mul, sub_zero]
  · intro hx
    obtain ⟨a, rfl⟩ := mem_span_singleton'.1 hx
    rw [RingHom.mem_ker, map_mul, hθξ, mul_zero]

end GlobalTheory
