import Mathlib

namespace GlobalTheory.SurjectiveOfKerSq

/- English proof (translation)
Establish `key : ∀ n : ℕ, I ≤ K ⊔ I ^ (n + 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `h2.trans (sup_le le_sup_left ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `key m` as an intermediate fact. Rewrite `this` using `[hnil, sup_bot_eq]`. Conclude with `le_antisymm this h1`.
-/
theorem eq_of_le_sup_sq {B : Type} [CommRing B] (I K : Ideal B) (m : ℕ)
    (hnil : I ^ (m + 1) = ⊥) (h1 : K ≤ I) (h2 : I ≤ K ⊔ I ^ 2) : I = K := by
  have key : ∀ n : ℕ, I ≤ K ⊔ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine h2.trans (sup_le le_sup_left ?_)
      calc I ^ 2 = I * I := pow_two I
        _ ≤ I * (K ⊔ I ^ (n + 1)) := Ideal.mul_mono_right ih
        _ = I * K ⊔ I ^ (n + 1 + 1) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ K ⊔ I ^ (n + 1 + 1) := sup_le_sup_right Ideal.mul_le_right _
  have := key m
  rw [hnil, sup_bot_eq] at this
  exact le_antisymm this h1

/- English proof (translation)
Establish `hI : RingHom.ker aug = Ideal.map f J` using `eq_of_le_sup_sq _ _ m hnil h1 h2`. Establish `base : ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug`. Introduce `b`. Use `⟨algebraMap V A (aug b), ?_⟩` and prove the remaining obligations. Simplify using `[RingHom.mem_ker]`.

Establish `step : ∀ n : ℕ, ∀ x ∈ RingHom.ker aug ^ n, ∀ b : B, ∃ a : A, b * x - f a ∈ RingHom.ker aug ^ (n + 1)`. Introduce `n x hx`. Establish `hpow : RingHom.ker aug ^ n = Ideal.span (f '' (J ^ n : Ideal A))`. Rewrite using `[hI, ← Ideal.map_pow]`. Both sides reduce to the same expression.

Establish `hx'` using `hx`. Rewrite `hx'` using `[hpow]`. Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy`.

Introduce `b`. Take `⟨j, hj, rfl⟩` from `hy`. Take `⟨a, ha⟩` from `base b`. Use `⟨a * j, ?_⟩` and prove the remaining obligations. Establish `hfj : f j ∈ RingHom.ker aug ^ n`.

Rewrite using `[hpow]`. Conclude with `Ideal.subset_span ⟨j, hj, rfl⟩`. Establish `e : b * f j - f (a * j) = f j * (b - f a)` using `by rw [map_mul]; ring`. Rewrite using `[e, pow_succ]`. Conclude with `Ideal.mul_mem_mul hfj ha`.

Consider the case `zero => intro b; exact ⟨0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Introduce `b`. Take `⟨a, ha⟩` from `hy b`. Take `⟨c, hc⟩` from `hz b`.

Use `⟨a + c, ?_⟩` and prove the remaining obligations. Establish `e : b * (y + z) - f (a + c) = (b * y - f a) + (b * z - f c)`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ ha hc`. Consider the case `smul c y _ hy`. Introduce `b`. Take `⟨a, ha⟩` from `hy (b * c)`. Conclude with `⟨a, by rwa [smul_eq_mul, ← mul_assoc]⟩`.

Establish `all : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro b; exact ⟨0, by simp⟩`. Consider the case `succ n ih`.

Introduce `b`. Take `⟨a, ha⟩` from `ih b`. Take `⟨c, hc⟩` from `step n _ ha 1`. Use `⟨a + c, ?_⟩` and prove the remaining obligations. Establish `e : b - f (a + c) = 1 * (b - f a) - f c` using `by rw [map_add]; ring`.

Rewrite using `[e]`. Conclude with `hc`. Introduce `b`. Take `⟨a, ha⟩` from `all (m + 1) b`. Rewrite `ha` using `[hnil, Ideal.mem_bot, sub_eq_zero]`.

Conclude with `⟨a, ha.symm⟩`.
-/
theorem surjective_of_ker_le_map_sup_sq {V : Type} [CommRing V] {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) (aug : B →ₐ[V] V) (m : ℕ)
    (hnil : RingHom.ker aug ^ (m + 1) = ⊥) (J : Ideal A)
    (h1 : Ideal.map f J ≤ RingHom.ker aug)
    (h2 : RingHom.ker aug ≤ Ideal.map f J ⊔ RingHom.ker aug ^ 2) :
    Function.Surjective f := by
  have hI : RingHom.ker aug = Ideal.map f J := eq_of_le_sup_sq _ _ m hnil h1 h2
  have base : ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug := by
    intro b
    refine ⟨algebraMap V A (aug b), ?_⟩
    simp [RingHom.mem_ker]
  have step : ∀ n : ℕ, ∀ x ∈ RingHom.ker aug ^ n, ∀ b : B,
      ∃ a : A, b * x - f a ∈ RingHom.ker aug ^ (n + 1) := by
    intro n x hx
    have hpow : RingHom.ker aug ^ n = Ideal.span (f '' (J ^ n : Ideal A)) := by
      rw [hI, ← Ideal.map_pow]; rfl
    have hx' := hx
    rw [hpow] at hx'
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      intro b
      obtain ⟨j, hj, rfl⟩ := hy
      obtain ⟨a, ha⟩ := base b
      refine ⟨a * j, ?_⟩
      have hfj : f j ∈ RingHom.ker aug ^ n := by
        rw [hpow]; exact Ideal.subset_span ⟨j, hj, rfl⟩
      have e : b * f j - f (a * j) = f j * (b - f a) := by rw [map_mul]; ring
      rw [e, pow_succ]
      exact Ideal.mul_mem_mul hfj ha
    | zero => intro b; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro b
      obtain ⟨a, ha⟩ := hy b
      obtain ⟨c, hc⟩ := hz b
      refine ⟨a + c, ?_⟩
      have e : b * (y + z) - f (a + c) = (b * y - f a) + (b * z - f c) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ ha hc
    | smul c y _ hy =>
      intro b
      obtain ⟨a, ha⟩ := hy (b * c)
      exact ⟨a, by rwa [smul_eq_mul, ← mul_assoc]⟩
  have all : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug ^ n := by
    intro n
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      obtain ⟨c, hc⟩ := step n _ ha 1
      refine ⟨a + c, ?_⟩
      have e : b - f (a + c) = 1 * (b - f a) - f c := by rw [map_add]; ring
      rw [e]
      exact hc
  intro b
  obtain ⟨a, ha⟩ := all (m + 1) b
  rw [hnil, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

end GlobalTheory.SurjectiveOfKerSq
