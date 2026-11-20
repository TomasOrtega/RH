import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hτ f hf g`. Establish `pm : ∀ x : K, hs (τ ^ 2 - 4) x = 1 ∨ hs (τ ^ 2 - 4) x = -1`. Introduce `x`. Unfold `hs`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hmul : ∀ a b : Kˣ, hs (τ ^ 2 - 4) ((a * b : Kˣ) : K) = hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (b : K)`. Introduce `a b`. Rewrite using `[Units.val_mul]`. Conclude with `hsMul O K Δ L _ a b hτ a.ne_zero b.ne_zero`. Establish `hone : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1`.

Unfold `hs`. Rewrite using `[if_pos]`. Conclude with `⟨1, 0, by simp⟩`. Establish `hsq : ∀ a : Kˣ, hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (a : K) = 1`. Introduce `a`.

Apply the tactic sequence `rcases pm (a : K) with h | h <;> rw [h] <;> norm_num`. Establish `hinv : ∀ a : Kˣ, hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K) = hs (τ ^ 2 - 4) (a : K)`. Introduce `a`. Establish `h` using `hmul a a⁻¹`. Rewrite `h` using `[mul_inv_cancel, hone]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsq, one_mul]`. Use `_ = hs (τ ^ 2 - 4) (a : K) := by rw [mul_assoc, ← h, mul_one]`. Establish `hmk : ∀ a b : Kˣ, (a : Kˣ ⧸ NE τ) = b ↔ hs (τ ^ 2 - 4) (a : K) = hs (τ ^ 2 - 4) (b : K)`. Introduce `a b`.

Rewrite using `[QuotientGroup.eq, hsNE O K Δ τ L hτ, hmul, hinv]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h, mul_one]`.

Use `_ = hs (τ ^ 2 - 4) (b : K) := by rw [← mul_assoc, hsq, one_mul]`. Introduce `h`. Rewrite using `[h, hsq]`. Establish `inv_of : ∀ φ : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, φ (t * x) = φ x) → ∀ a b : Kˣ, (a : Kˣ ⧸ NE τ) = b → φ a = φ b`. Introduce `φ hφ a b h`.

Establish `h'` using `QuotientGroup.eq.1 h`. Establish `e : b = (a⁻¹ * b) * a` using `((mul_comm _ _).trans (mul_inv_cancel_left a b)).symm`. Rewrite using `[e, hφ _ h']`. Use `haveI : Finite (Kˣ ⧸ NE τ) := by`. Use `Finite.of_injective (fun q : Kˣ ⧸ NE τ => decide (hs (τ ^ 2 - 4) ((Quotient.out q : Kˣ) : K) = 1)) ?_` and prove the remaining obligations.

Introduce `p q hpq`. Establish `key : ((Quotient.out p : Kˣ) : Kˣ ⧸ NE τ) = (Quotient.out q : Kˣ)`. Rewrite using `[hmk]`. Simplify using `only [decide_eq_decide] at hpq`. Apply the tactic sequence `rcases pm ((Quotient.out p : Kˣ) : K) with h1 | h1 <;> rcases pm ((Quotient.out q : Kˣ) : K) with h2 | h2 <;> (rw [h1, h2] at hpq ⊢; try norm_num at hpq)`.

Simplify using `using key`. Establish `shift : ∀ φ : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, φ (t * x) = φ x) → ∑ᶠ t : Kˣ ⧸ NE τ, φ (Quotient.out t * g) = ∑ᶠ t : Kˣ ⧸ NE τ, φ (Quotient.out t)`. Introduce `φ hφ`. Establish `e : ∀ t : Kˣ ⧸ NE τ, φ (Quotient.out t * g) = φ (Quotient.out (t * (g : Kˣ ⧸ NE τ)))`. Introduce `t`.

Apply `inv_of φ hφ` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[finsum_congr e]`. Conclude with `finsum_comp_equiv (f := fun q : Kˣ ⧸ NE τ => φ (Quotient.out q)) (Equiv.mulRight (g : Kˣ ⧸ NE τ))`. Use `⟨shift f hf, ?_, ?_⟩` and prove the remaining obligations.

Establish `hφ : ∀ t ∈ NE τ, ∀ x : Kˣ, hs (τ ^ 2 - 4) ((t * x : Kˣ) : K) * f (t * x) = hs (τ ^ 2 - 4) (x : K) * f x`. Introduce `t ht x`. Rewrite using `[hmul, (hsNE O K Δ τ L hτ t).1 ht, one_mul, hf t ht]`. Establish `e : ∀ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K) * f (Quotient.out t * g) = hs (τ ^ 2 - 4) (g : K) * (hs (τ ^ 2 - 4) ((Quotient.out t * g : Kˣ) : K) * f (Quotient.out t * g))`. Introduce `t`.

Rewrite using `[hmul]`. Take the linear combination `(-(hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K) * f (Quotient.out t * g))) * hsq g`. Rewrite using `[finsum_congr e, ← mul_finsum, shift (fun x : Kˣ => hs (τ ^ 2 - 4) (x : K) * f x) hφ]`. Introduce `e x hfx ⟨t0, ht0⟩`. Establish `hq : ∀ q : Kˣ ⧸ NE τ, q ≠ (t0 : Kˣ ⧸ NE τ) → hs (τ ^ 2 - 4) ((Quotient.out q : Kˣ) : K) ≠ e`.

Introduce `q hq h`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' q]`. Conclude with `(hmk _ _).2 (h.trans ht0.symm)`. Establish `h0 : hs (τ ^ 2 - 4) ((Quotient.out (t0 : Kˣ ⧸ NE τ) : Kˣ) : K) = e`.

Rewrite using `[← ht0]`. Conclude with `(hmk _ _).1 (by simp)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[finsum_eq_single _ (t0 : Kˣ ⧸ NE τ)]`. Rewrite using `[hfx, if_pos h0]`.

Introduce `q hq'`. Rewrite using `[hfx, if_neg (hq q hq')]`. Rewrite using `[finsum_eq_single _ (t0 : Kˣ ⧸ NE τ)]`. Rewrite using `[hfx, if_pos h0, h0]`. Introduce `q hq'`.

Rewrite using `[hfx, if_neg (hq q hq'), mul_zero]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.sumShift : UpperTheory.V.Z.Sym.Loc.SumShift := by
  intro O K _ _ _ _ _ Δ τ L hτ f hf g
  have pm : ∀ x : K, hs (τ ^ 2 - 4) x = 1 ∨ hs (τ ^ 2 - 4) x = -1 := by
    intro x
    unfold hs
    split_ifs <;> simp
  have hmul : ∀ a b : Kˣ, hs (τ ^ 2 - 4) ((a * b : Kˣ) : K) = hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (b : K) := by
    intro a b
    rw [Units.val_mul]
    exact hsMul O K Δ L _ a b hτ a.ne_zero b.ne_zero
  have hone : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1 := by
    unfold hs
    rw [if_pos]
    exact ⟨1, 0, by simp⟩
  have hsq : ∀ a : Kˣ, hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (a : K) = 1 := by
    intro a
    rcases pm (a : K) with h | h <;> rw [h] <;> norm_num
  have hinv : ∀ a : Kˣ, hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K) = hs (τ ^ 2 - 4) (a : K) := by
    intro a
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    calc hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K)
        = hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K) := by
          rw [hsq, one_mul]
      _ = hs (τ ^ 2 - 4) (a : K) := by rw [mul_assoc, ← h, mul_one]
  have hmk : ∀ a b : Kˣ, (a : Kˣ ⧸ NE τ) = b ↔ hs (τ ^ 2 - 4) (a : K) = hs (τ ^ 2 - 4) (b : K) := by
    intro a b
    rw [QuotientGroup.eq, hsNE O K Δ τ L hτ, hmul, hinv]
    constructor
    · intro h
      calc hs (τ ^ 2 - 4) (a : K) = hs (τ ^ 2 - 4) (a : K) * (hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (b : K)) := by
            rw [h, mul_one]
        _ = hs (τ ^ 2 - 4) (b : K) := by rw [← mul_assoc, hsq, one_mul]
    · intro h
      rw [h, hsq]
  have inv_of : ∀ φ : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, φ (t * x) = φ x) →
      ∀ a b : Kˣ, (a : Kˣ ⧸ NE τ) = b → φ a = φ b := by
    intro φ hφ a b h
    have h' := QuotientGroup.eq.1 h
    have e : b = (a⁻¹ * b) * a := ((mul_comm _ _).trans (mul_inv_cancel_left a b)).symm
    rw [e, hφ _ h']
  haveI : Finite (Kˣ ⧸ NE τ) := by
    refine Finite.of_injective (fun q : Kˣ ⧸ NE τ => decide (hs (τ ^ 2 - 4) ((Quotient.out q : Kˣ) : K) = 1)) ?_
    intro p q hpq
    have key : ((Quotient.out p : Kˣ) : Kˣ ⧸ NE τ) = (Quotient.out q : Kˣ) := by
      rw [hmk]
      simp only [decide_eq_decide] at hpq
      rcases pm ((Quotient.out p : Kˣ) : K) with h1 | h1 <;> rcases pm ((Quotient.out q : Kˣ) : K) with h2 | h2 <;>
        (rw [h1, h2] at hpq ⊢; try norm_num at hpq)
    simpa using key
  have shift : ∀ φ : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, φ (t * x) = φ x) →
      ∑ᶠ t : Kˣ ⧸ NE τ, φ (Quotient.out t * g) = ∑ᶠ t : Kˣ ⧸ NE τ, φ (Quotient.out t) := by
    intro φ hφ
    have e : ∀ t : Kˣ ⧸ NE τ, φ (Quotient.out t * g) = φ (Quotient.out (t * (g : Kˣ ⧸ NE τ))) := by
      intro t
      apply inv_of φ hφ
      simp
    rw [finsum_congr e]
    exact finsum_comp_equiv (f := fun q : Kˣ ⧸ NE τ => φ (Quotient.out q)) (Equiv.mulRight (g : Kˣ ⧸ NE τ))
  refine ⟨shift f hf, ?_, ?_⟩
  · have hφ : ∀ t ∈ NE τ, ∀ x : Kˣ, hs (τ ^ 2 - 4) ((t * x : Kˣ) : K) * f (t * x) = hs (τ ^ 2 - 4) (x : K) * f x := by
      intro t ht x
      rw [hmul, (hsNE O K Δ τ L hτ t).1 ht, one_mul, hf t ht]
    have e : ∀ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K) * f (Quotient.out t * g) =
        hs (τ ^ 2 - 4) (g : K) * (hs (τ ^ 2 - 4) ((Quotient.out t * g : Kˣ) : K) * f (Quotient.out t * g)) := by
      intro t
      rw [hmul]
      linear_combination (-(hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K) * f (Quotient.out t * g))) * hsq g
    rw [finsum_congr e, ← mul_finsum,
      shift (fun x : Kˣ => hs (τ ^ 2 - 4) (x : K) * f x) hφ]
  · intro e x hfx ⟨t0, ht0⟩
    have hq : ∀ q : Kˣ ⧸ NE τ, q ≠ (t0 : Kˣ ⧸ NE τ) → hs (τ ^ 2 - 4) ((Quotient.out q : Kˣ) : K) ≠ e := by
      intro q hq h
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (hmk _ _).2 (h.trans ht0.symm)
    have h0 : hs (τ ^ 2 - 4) ((Quotient.out (t0 : Kˣ ⧸ NE τ) : Kˣ) : K) = e := by
      rw [← ht0]
      exact (hmk _ _).1 (by simp)
    constructor
    · rw [finsum_eq_single _ (t0 : Kˣ ⧸ NE τ)]
      · rw [hfx, if_pos h0]
      · intro q hq'
        rw [hfx, if_neg (hq q hq')]
    · rw [finsum_eq_single _ (t0 : Kˣ ⧸ NE τ)]
      · rw [hfx, if_pos h0, h0]
      · intro q hq'
        rw [hfx, if_neg (hq q hq'), mul_zero]
