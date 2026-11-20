import Formalism.WachLatticeTwists.HodgeTateChains.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, _, rfl⟩`. Conclude with `⟨b, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, trivial, rfl⟩`.
-/
lemma mem_pow_smul_top {R : Type} [CommRing R] {Xm : Type} [AddCommGroup Xm] [Module R Xm] (ϖ : R)
    (n : ℕ) (x : Xm) :
    x ∈ ((Ideal.span {ϖ}) ^ n • (⊤ : Submodule R Xm)) ↔ ∃ y, x = ϖ ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, _, rfl⟩; exact ⟨b, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, trivial, rfl⟩

/- English proof (translation)
Apply `hc.toIsHausdorff.haus` to reduce the goal to its premises. Introduce `n`. Rewrite using `[SModEq.zero, mem_pow_smul_top]`. Conclude with `h n`.
-/
lemma haus_of {R : Type} [CommRing R] {Xm : Type} [AddCommGroup Xm] [Module R Xm] (ϖ : R)
    (hc : IsAdicComplete (Ideal.span {ϖ}) Xm) (x : Xm) (h : ∀ n : ℕ, ∃ y, x = ϖ ^ n • y) : x = 0 := by
  apply hc.toIsHausdorff.haus
  intro n
  rw [SModEq.zero, mem_pow_smul_top]
  exact h n

/- English proof (translation)
Introduce `R _ Xm _ _ ϖ hc E`. Prove the components needed by the constructor for the conclusion. Introduce `x x' hxx`. Establish `hd : x - x' = -(ϖ • E (x - x'))`. Establish `h : x + ϖ • E x = x' + ϖ • E x'` using `hxx`.

Rewrite using `[map_sub, smul_sub, neg_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]`. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `haus_of ϖ hc` to reduce the goal to its premises. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => exact ⟨x - x', by simp⟩`. Consider the case `succ n ih`. Take `⟨y, hy⟩` from `ih`. Use `⟨-(E y), ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`.

Use `conv_lhs => rw [hy]`. Rewrite using `[map_smul, smul_smul, ← pow_succ', smul_neg]`. Introduce `y`. Set `a : ℕ → Xm` to `fun n => (fun v => -(E v))^[n] y`. Establish `ha0 : a 0 = y` using `rfl`.

Establish `has : ∀ n, a (n + 1) = -(E (a n))` using `fun n => Function.iterate_succ_apply' _ _ _`. Set `f : ℕ → Xm` to `fun n => ∑ k ∈ Finset.range n, ϖ ^ k • a k`. Establish `hfs : ∀ n, f (n + 1) = f n + ϖ ^ n • a n` using `fun n => Finset.sum_range_succ _ _`. Establish `hid : ∀ n, f n + ϖ • E (f n) = y - ϖ ^ n • a n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp [f, ha0]`. Consider the case `succ n ih`. Rewrite using `[hfs, map_add, smul_add, has, map_smul, smul_smul, ← pow_succ', smul_neg]`. Establish `: f n + ϖ ^ n • a n + (ϖ • E (f n) + ϖ ^ (n + 1) • E (a n)) = (f n + ϖ • E (f n)) + ϖ ^ n • a n + ϖ ^ (n + 1) • E (a n)` using `by abel`.

Rewrite using `[this, ih]`. Normalize the expressions using the abelian group laws. Establish `hcau : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD ((Ideal.span {ϖ}) ^ m • (⊤ : Submodule R Xm))]`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, mem_pow_smul_top]`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => exact ⟨0, by simp⟩`. Consider the case `succ n hmn ih`. Take `⟨t, ht⟩` from `ih`. Use `⟨t - ϖ ^ (n - m) • a n, ?_⟩` and prove the remaining obligations.

Rewrite using `[hfs, smul_sub, ← ht, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]`. Normalize the expressions using the abelian group laws. Take `⟨L, hL⟩` from `hc.toIsPrecomplete.prec hcau`. Use `⟨L, ?_⟩` and prove the remaining obligations. Apply `sub_eq_zero.1` to reduce the goal to its premises.

Apply `haus_of ϖ hc` to reduce the goal to its premises. Introduce `n`. Establish `h1` using `hL n`. Rewrite `h1` using `[SModEq.sub_mem, mem_pow_smul_top]`. Take `⟨t, ht⟩` from `h1`.

Use `⟨-(t + ϖ • E t) - a n, ?_⟩` and prove the remaining obligations. Establish `hLf : L = f n - ϖ ^ n • t` using `by rw [← ht]; abel`. Establish `h2 : L + ϖ • E L - y = (f n + ϖ • E (f n)) - y - (ϖ ^ n • t + ϖ • E (ϖ ^ n • t))`. Rewrite using `[hLf, map_sub, smul_sub]`. Normalize the expressions using the abelian group laws.

Use `show L + ϖ • E L - y = _`. Rewrite using `[h2, hid, map_smul, smul_sub, smul_neg, smul_add, smul_comm ϖ (ϖ ^ n)]`. Normalize the expressions using the abelian group laws.
-/
theorem onePlus : StatOnePlus := by
  intro R _ Xm _ _ ϖ hc E
  constructor
  · intro x x' hxx
    have hd : x - x' = -(ϖ • E (x - x')) := by
      have h : x + ϖ • E x = x' + ϖ • E x' := hxx
      rw [map_sub, smul_sub, neg_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]
    apply sub_eq_zero.1
    apply haus_of ϖ hc
    intro n
    induction n with
    | zero => exact ⟨x - x', by simp⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨-(E y), ?_⟩
      rw [hd]
      conv_lhs => rw [hy]
      rw [map_smul, smul_smul, ← pow_succ', smul_neg]
  · intro y
    let a : ℕ → Xm := fun n => (fun v => -(E v))^[n] y
    have ha0 : a 0 = y := rfl
    have has : ∀ n, a (n + 1) = -(E (a n)) := fun n => Function.iterate_succ_apply' _ _ _
    let f : ℕ → Xm := fun n => ∑ k ∈ Finset.range n, ϖ ^ k • a k
    have hfs : ∀ n, f (n + 1) = f n + ϖ ^ n • a n := fun n => Finset.sum_range_succ _ _
    have hid : ∀ n, f n + ϖ • E (f n) = y - ϖ ^ n • a n := by
      intro n
      induction n with
      | zero => simp [f, ha0]
      | succ n ih =>
        rw [hfs, map_add, smul_add, has, map_smul, smul_smul, ← pow_succ', smul_neg]
        have : f n + ϖ ^ n • a n + (ϖ • E (f n) + ϖ ^ (n + 1) • E (a n))
            = (f n + ϖ • E (f n)) + ϖ ^ n • a n + ϖ ^ (n + 1) • E (a n) := by abel
        rw [this, ih]; abel
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n [SMOD ((Ideal.span {ϖ}) ^ m • (⊤ : Submodule R Xm))] := by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top]
      induction n, hmn using Nat.le_induction with
      | base => exact ⟨0, by simp⟩
      | succ n hmn ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨t - ϖ ^ (n - m) • a n, ?_⟩
        rw [hfs, smul_sub, ← ht, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
        abel
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    apply sub_eq_zero.1
    apply haus_of ϖ hc
    intro n
    have h1 := hL n
    rw [SModEq.sub_mem, mem_pow_smul_top] at h1
    obtain ⟨t, ht⟩ := h1
    refine ⟨-(t + ϖ • E t) - a n, ?_⟩
    have hLf : L = f n - ϖ ^ n • t := by rw [← ht]; abel
    have h2 : L + ϖ • E L - y = (f n + ϖ • E (f n)) - y - (ϖ ^ n • t + ϖ • E (ϖ ^ n • t)) := by
      rw [hLf, map_sub, smul_sub]; abel
    show L + ϖ • E L - y = _
    rw [h2, hid, map_smul, smul_sub, smul_neg, smul_add, smul_comm ϖ (ϖ ^ n)]
    abel

/- English proof (translation)
Introduce `R _ Xm _ _ ϖ z hc hz g S B hgS hSg`. Establish `hb` using `h1 R Xm ϖ hc (S ∘ₗ B ∘ₗ g)`. Establish `key : ∀ x, (g x + (z * ϖ) • B (g x)) - x = g (x + ϖ • S (B (g x))) - (x + ϖ • S (B (g x)))`. Introduce `x`. Establish `h` using `hgS (B (g x))`.

Rewrite using `[map_add, map_smul, mul_comm z ϖ, mul_smul, ← h, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hinj : ∀ x, g x = x → x = 0` using `fun x hx => hz x (by rw [← hSg, hx, sub_self, map_zero])`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `h0 : g (x + ϖ • S (B (g x))) = x + ϖ • S (B (g x))` using `sub_eq_zero.1 (by rw [← key, hx, sub_self])`. Establish `h2` using `hinj _ h0`. Apply `hb.1` to reduce the goal to its premises. Use `show x + ϖ • S (B (g x)) = 0 + ϖ • S (B (g 0))`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨_, key x⟩`.

Introduce and unpack `⟨x, rfl⟩`. Take `⟨x', hx'⟩` from `hb.2 x`. Establish `hx'' : x' + ϖ • S (B (g x')) = x` using `hx'`. Conclude with `⟨x', by rw [key, hx'']⟩`. Introduce `x`.

Take `⟨x', hx'⟩` from `hb.2 (S x)`. Establish `hx'' : x' + ϖ • S (B (g x')) = S x` using `hx'`. Conclude with `⟨x', by rw [key, hx'', hgS]⟩`.
-/
theorem third_estimate_of_first_two (h1 : StatOnePlus) : PerturbationOperatorIntegral := by
  intro R _ Xm _ _ ϖ z hc hz g S B hgS hSg
  have hb := h1 R Xm ϖ hc (S ∘ₗ B ∘ₗ g)
  have key : ∀ x, (g x + (z * ϖ) • B (g x)) - x
      = g (x + ϖ • S (B (g x))) - (x + ϖ • S (B (g x))) := by
    intro x
    have h := hgS (B (g x))
    rw [map_add, map_smul, mul_comm z ϖ, mul_smul, ← h, smul_sub]; abel
  have hinj : ∀ x, g x = x → x = 0 := fun x hx => hz x (by rw [← hSg, hx, sub_self, map_zero])
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have h0 : g (x + ϖ • S (B (g x))) = x + ϖ • S (B (g x)) :=
      sub_eq_zero.1 (by rw [← key, hx, sub_self])
    have h2 := hinj _ h0
    apply hb.1
    show x + ϖ • S (B (g x)) = 0 + ϖ • S (B (g 0))
    rw [h2]; simp
  · intro y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, key x⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := hb.2 x
      have hx'' : x' + ϖ • S (B (g x')) = x := hx'
      exact ⟨x', by rw [key, hx'']⟩
  · intro x
    obtain ⟨x', hx'⟩ := hb.2 (S x)
    have hx'' : x' + ϖ • S (B (g x')) = S x := hx'
    exact ⟨x', by rw [key, hx'', hgS]⟩

/- English proof (translation)
The claim follows from `third_estimate_of_first_two onePlus`.
-/
theorem t3 : PerturbationOperatorIntegral := third_estimate_of_first_two onePlus

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
