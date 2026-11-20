import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

open Classical in
/- English proof (translation)
Establish `step : ∀ g, (if t - g ∈ A0 then θ g else 0) = if t - g ∈ A0 then θ t else 0`. Introduce `g`. Use `split_ifs with hg`. Establish `e : g = t + -(t - g)` using `by abel`. Rewrite using `[e, AddChar.map_add_eq_mul, h0 _ (A0.neg_mem hg), mul_one]`.

Both sides reduce to the same expression. Establish `eqv : A0 ≃ {g : H // t - g ∈ A0}` using `{ toFun := fun s => ⟨t - s, by simpa using s.2⟩ invFun := fun g => ⟨t - g, g.2⟩ left_inv := fun s => by ext; simp right_inv := fun g => by ext; simp }`. Establish `hc : (Finset.univ.filter fun g => t - g ∈ A0).card = Nat.card A0`. Rewrite using `[Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Rewrite using `[Finset.sum_congr rfl fun g _ => step g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]`.
-/
private theorem tops_sum_coset {H : Type} [AddCommGroup H] [Fintype H] (A0 : AddSubgroup H) (θ : AddChar H ℂ)
    (h0 : ∀ s ∈ A0, θ s = 1) (t : H) :
    ∑ g : H, (if t - g ∈ A0 then θ g else 0) = (Nat.card A0 : ℂ) * θ t := by
  have step : ∀ g, (if t - g ∈ A0 then θ g else 0) = if t - g ∈ A0 then θ t else 0 := by
    intro g
    split_ifs with hg
    · have e : g = t + -(t - g) := by abel
      rw [e, AddChar.map_add_eq_mul, h0 _ (A0.neg_mem hg), mul_one]
    · rfl
  have eqv : A0 ≃ {g : H // t - g ∈ A0} :=
    { toFun := fun s => ⟨t - s, by simpa using s.2⟩
      invFun := fun g => ⟨t - g, g.2⟩
      left_inv := fun s => by ext; simp
      right_inv := fun g => by ext; simp }
  have hc : (Finset.univ.filter fun g => t - g ∈ A0).card = Nat.card A0 := by
    rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl fun g _ => step g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]

open Classical in
/- English proof (translation)
Establish `hiff : ∀ g : H, 0 - g ∈ A0 ↔ g ∈ A0` using `fun g => by rw [zero_sub, neg_mem_iff]`. Establish `hz` using `tops_sum_coset A0 θ h0 0`. Simplify using `only [hiff, AddChar.map_zero_eq_one, mul_one] at hz`. Establish `hB : ∑ g, θ g = 0` using `AddChar.sum_eq_zero_iff_ne_zero.mpr h1`. Establish `hC : ∑ g, θ g * (if g ∈ A0 then (c : ℂ) else 0) = (Nat.card A0 : ℂ) * c`.

Rewrite using `[← hz, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Establish `hA : ∑ g, θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ) = (Nat.card A0 : ℂ) * ∑ t ∈ TT, θ t`. Rewrite using `[Finset.mul_sum, Finset.sum_congr rfl fun t _ => (tops_sum_coset A0 θ h0 t).symm, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]`. Take `⟨e, he⟩ : ∃ e : H → ℝ, ∀ g, e g = ((TT.filter fun t => t - g ∈ A0).card : ℝ) - (b + if g ∈ A0 then c else 0)` from `⟨_, fun _ => rfl⟩`. Establish `key : (Nat.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c) = ∑ g, θ g * ((e g : ℝ) : ℂ)`. Establish `hsplit : ∀ g, θ g * ((e g : ℝ) : ℂ) = θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ) - (b : ℂ) * θ g - θ g * (if g ∈ A0 then (c : ℂ) else 0)`.

Introduce `g`. Rewrite using `[he g]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Rewrite using `[Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hA, ← Finset.mul_sum, hB, hC]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnorm : ∀ g, ‖θ g‖ = 1`. Introduce `g`. Establish `hp : θ g ^ Fintype.card H = 1`. Rewrite using `[← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]`. Establish `hq : ‖θ g‖ ^ Fintype.card H = 1` using `by rw [← norm_pow, hp, norm_one]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hq`. Establish `hbound : ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ ≤ Fintype.card H * η`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs, he g]`. Conclude with `hs g`.

Use `_ = Fintype.card H * η := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hn : (0 : ℝ) < Nat.card A0` using `by exact_mod_cast Nat.card_pos`. Establish `h3 : (Nat.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ (Nat.card A0 : ℝ) * (o * η)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_left h3 hn`.
-/
private theorem tops_sum_gen {H : Type} [AddCommGroup H] [Fintype H] (A0 : AddSubgroup H) (θ : AddChar H ℂ)
    (h0 : ∀ s ∈ A0, θ s = 1) (h1 : θ ≠ 0) (TT : Finset H) (o : ℕ) (ho : Fintype.card H = o * Nat.card A0)
    (b c η : ℝ)
    (hs : ∀ g : H, |((TT.filter fun t => t - g ∈ A0).card : ℝ) - (b + if g ∈ A0 then c else 0)| ≤ η) :
    ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ o * η := by
  have hiff : ∀ g : H, 0 - g ∈ A0 ↔ g ∈ A0 := fun g => by rw [zero_sub, neg_mem_iff]
  have hz := tops_sum_coset A0 θ h0 0
  simp only [hiff, AddChar.map_zero_eq_one, mul_one] at hz
  have hB : ∑ g, θ g = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr h1
  have hC : ∑ g, θ g * (if g ∈ A0 then (c : ℂ) else 0) = (Nat.card A0 : ℂ) * c := by
    rw [← hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring
  have hA : ∑ g, θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ) = (Nat.card A0 : ℂ) * ∑ t ∈ TT, θ t := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun t _ => (tops_sum_coset A0 θ h0 t).symm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  obtain ⟨e, he⟩ : ∃ e : H → ℝ, ∀ g, e g =
      ((TT.filter fun t => t - g ∈ A0).card : ℝ) - (b + if g ∈ A0 then c else 0) := ⟨_, fun _ => rfl⟩
  have key : (Nat.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c) = ∑ g, θ g * ((e g : ℝ) : ℂ) := by
    have hsplit : ∀ g, θ g * ((e g : ℝ) : ℂ) = θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ)
        - (b : ℂ) * θ g - θ g * (if g ∈ A0 then (c : ℂ) else 0) := by
      intro g
      rw [he g]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hA,
      ← Finset.mul_sum, hB, hC]
    ring
  have hnorm : ∀ g, ‖θ g‖ = 1 := by
    intro g
    have hp : θ g ^ Fintype.card H = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have hq : ‖θ g‖ ^ Fintype.card H = 1 := by rw [← norm_pow, hp, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hq
  have hbound : ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ ≤ Fintype.card H * η := by
    calc ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ ≤ ∑ g, ‖θ g * ((e g : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g : H, η := Finset.sum_le_sum fun g _ => by
          rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs, he g]
          exact hs g
      _ = Fintype.card H * η := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Nat.card A0 := by exact_mod_cast Nat.card_pos
  have h3 : (Nat.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ (Nat.card A0 : ℝ) * (o * η) := by
    calc (Nat.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖
        = ‖(Nat.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c)‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ := by rw [key]
      _ ≤ Fintype.card H * η := hbound
      _ = (Nat.card A0 : ℝ) * (o * η) := by rw [ho]; push_cast; ring
  exact le_of_mul_le_mul_left h3 hn

/- English proof (translation)
Introduce `φ TT δ hsh ψ hψ hnt`. Establish `hmem : ∀ s ∈ φ.A0, ψ (0, s) = 1`. Simplify `hψ` using `[PsiA]`. Set `θ : AddChar φ.A ℂ` to `ψ.compAddMonoidHom (AddMonoidHom.inr E0 φ.A)`. Establish `hθ : ∀ t, θ t = ψ (0, t)` using `fun t => rfl`.

Establish `h1 : θ ≠ 0`. Introduce `h`. Apply `hnt` to reduce the goal to its premises. Introduce `t`. Rewrite using `[← hθ, h, AddChar.zero_apply]`.

Establish `ho : Fintype.card φ.A = φ.o * Nat.card φ.A0`. Rewrite using `[Frame.card_A, Frame.natCard_cyclic_subgroup, Frame.exponent_eq_index_mul_cyclic_order]`. Establish `hpos : (0 : ℝ) < 3 * (φ.o : ℝ) + 1` using `by positivity`. Establish `hs : ∀ g : φ.A, |((TT.filter fun t => t - g ∈ φ.A0).card : ℝ) - (3 * (3 * (φ.o : ℝ) + 1)⁻¹ * TT.card + if g ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ * TT.card else 0)| ≤ δ * TT.card`. Introduce `g`.

Establish `hg` using `hsh g`. Use `hg using 3` and compare the differences between its conclusion and the goal. Simplify using `only [Frame.lam]`. Apply the tactic sequence `split_ifs <;> field_simp <;> ring`. Establish `hfin` using `tops_sum_gen φ.A0 θ (fun s hs => by rw [hθ]; exact hmem s hs) h1 TT φ.o ho _ _ _ hs`.

Simplify using `only [hθ] at hfin`. Move the coercions through the operations in `at hfin ⊢`. Conclude with `le_of_le_of_eq hfin (by ring)`.
-/
theorem UpperTheory.Comparison₂.tops_sum :
    ∀ (φ : Frame) (TT : Finset φ.A) (δ : ℝ), φ.Shares TT δ → ∀ ψ ∈ PsiA φ.A0, (¬ ∀ h : φ.A, ψ (0, h) = 1) →
      ‖(∑ t ∈ TT, ψ (0, t)) - (((3 * (φ.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤ φ.o * δ * (TT.card : ℝ) := by
  classical
  intro φ TT δ hsh ψ hψ hnt
  have hmem : ∀ s ∈ φ.A0, ψ (0, s) = 1 := by
    simpa [PsiA] using hψ
  let θ : AddChar φ.A ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr E0 φ.A)
  have hθ : ∀ t, θ t = ψ (0, t) := fun t => rfl
  have h1 : θ ≠ 0 := by
    intro h
    apply hnt
    intro t
    rw [← hθ, h, AddChar.zero_apply]
  have ho : Fintype.card φ.A = φ.o * Nat.card φ.A0 := by
    rw [Frame.card_A, Frame.natCard_cyclic_subgroup, Frame.exponent_eq_index_mul_cyclic_order]
  have hpos : (0 : ℝ) < 3 * (φ.o : ℝ) + 1 := by positivity
  have hs : ∀ g : φ.A, |((TT.filter fun t => t - g ∈ φ.A0).card : ℝ) -
      (3 * (3 * (φ.o : ℝ) + 1)⁻¹ * TT.card + if g ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ * TT.card else 0)|
        ≤ δ * TT.card := by
    intro g
    have hg := hsh g
    convert hg using 3
    simp only [Frame.lam]
    split_ifs <;> field_simp <;> ring
  have hfin := tops_sum_gen φ.A0 θ (fun s hs => by rw [hθ]; exact hmem s hs) h1 TT φ.o ho _ _ _ hs
  simp only [hθ] at hfin
  push_cast at hfin ⊢
  exact le_of_le_of_eq hfin (by ring)
