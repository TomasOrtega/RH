import Mathlib

/- English proof (translation)
Introduce `O σ _ _ f hf`. Establish `hex : ∀ m : σ →₀ ℕ, m ≠ 0 → ∃ i, m i ≠ 0`. Introduce `m hm`. Assume the negation of the conclusion as `h`. Apply `hm` to reduce the goal to its premises.

Use extensionality with `i`. Assume the negation of the conclusion as `hi`. Conclude with `h ⟨i, hi⟩`. Use `choose c hc using hex`. Set `p : (σ →₀ ℕ) → σ → Prop` to `fun m i => ∃ hm : m ≠ 0, c m hm = i`.

Set `g : σ → MvPowerSeries σ O` to `fun i n => if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f else 0`. Establish `hg : ∀ i n, MvPowerSeries.coeff n (g i) = if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f else 0` using `fun _ _ => rfl`. Establish `key : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * g i) = if p m i then MvPowerSeries.coeff m f else 0`. Introduce `i m`. Rewrite using `[MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]`.

Distinguish the cases in `h : Finsupp.single i 1 ≤ m`. Rewrite using `[if_pos h, one_mul, hg, tsub_add_cancel_of_le h]`. Rewrite using `[if_neg h, if_neg]`. Introduce and unpack `⟨hm, hi⟩`. Apply `h` to reduce the goal to its premises.

Rewrite using `[Finsupp.single_le_iff, ← hi]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (hc m hm)`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[map_sum]`.

Simplify using `only [key]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_eq_single (c m hm)]`. Rewrite using `[if_pos ⟨hm, rfl⟩]`. Introduce `j _ hj`. Rewrite using `[if_neg]`. Introduce and unpack `⟨_, h⟩`.

Conclude with `hj h.symm`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) →
      ∃ (g : σ → MvPowerSeries σ O), f = ∑ i : σ, MvPowerSeries.X i * g i := by
  intro O σ _ _ f hf
  classical
  have hex : ∀ m : σ →₀ ℕ, m ≠ 0 → ∃ i, m i ≠ 0 := by
    intro m hm
    by_contra h
    apply hm
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  choose c hc using hex
  let p : (σ →₀ ℕ) → σ → Prop := fun m i => ∃ hm : m ≠ 0, c m hm = i
  let g : σ → MvPowerSeries σ O := fun i n =>
    if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f else 0
  have hg : ∀ i n, MvPowerSeries.coeff n (g i) =
      if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f
      else 0 := fun _ _ => rfl
  have key : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * g i) =
      if p m i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : Finsupp.single i 1 ≤ m
    · rw [if_pos h, one_mul, hg, tsub_add_cancel_of_le h]
    · rw [if_neg h, if_neg]
      rintro ⟨hm, hi⟩
      apply h
      rw [Finsupp.single_le_iff, ← hi]
      exact Nat.one_le_iff_ne_zero.mpr (hc m hm)
  refine ⟨g, ?_⟩
  ext m
  rw [map_sum]
  simp only [key]
  by_cases hm : m = 0
  · subst hm
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    simp
  · rw [Finset.sum_eq_single (c m hm)]
    · rw [if_pos ⟨hm, rfl⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hj h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
