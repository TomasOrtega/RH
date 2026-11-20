import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hτ hs0`. Establish `hN` using `hsNE O K Δ τ L hτ`. Use `⟨?_, fun f hf g hg => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, h⟩` from `(hsLaw O K Δ L).2.2.1 _ hτ hs0`. Conclude with `⟨Units.mk0 x hx, fun h' => by have := (hN _).1 h'; rw [Units.val_mk0, h] at this; norm_num at this⟩`.

Establish `neg : ∀ t : Kˣ, t ∉ NE τ → hs (τ ^ 2 - 4) (t : K) = -1` using `fun t ht => by`. Use `mt (hN t).2 ht` as an intermediate fact. Unfold `hs at this ⊢`. Use `split_ifs at this ⊢ with h`. Conclude with `absurd rfl this`.

Both sides reduce to the same expression. Establish `out : ∀ x : Kˣ, f (x : Kˣ ⧸ NE τ).out = f x` using `fun x => by`. Establish `: x⁻¹ * (x : Kˣ ⧸ NE τ).out ∈ NE τ` using `QuotientGroup.eq.1 (by simp)`. Rewrite using `[← hf _ this x, mul_comm _ x, mul_inv_cancel_left]`. Establish `hne : ((1 : Kˣ) : Kˣ ⧸ NE τ) ≠ (g : Kˣ ⧸ NE τ)` using `fun h => hg (by simpa using QuotientGroup.eq.1 h)`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := {((1 : Kˣ) : Kˣ ⧸ NE τ), (g : Kˣ ⧸ NE τ)}) _ fun t _ => ?_, Finset.sum_pair hne, out, out]`. Proceed by induction on `t using QuotientGroup.induction_on with`. Consider the case `H t`. Simplify using `only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]`. Distinguish the cases in `ht : t ∈ NE τ`.

Conclude with `.inl (QuotientGroup.eq.2 (by simpa using ht))`. Use `.inr (QuotientGroup.eq.2 ((hN _).2 ?_))` and prove the remaining obligations. Rewrite using `[Units.val_mul, hsMul O K Δ L _ _ _ hτ (Units.ne_zero _) g.ne_zero, neg _ hg, neg _ fun h => ht (by simpa using h)]`. Evaluate the numerical expressions.
-/
theorem UpperTheory.finsum_quotient_norms_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → (∃ g : Kˣ, g ∉ NE τ) ∧ ∀ f : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, f (t * x) = f x) → ∀ g : Kˣ, g ∉ NE τ → (∑ᶠ t : Kˣ ⧸ NE τ, f t.out) = f 1 + f g := by
  intro O K _ _ _ _ _ Δ τ L hτ hs0
  classical
  have hN := hsNE O K Δ τ L hτ
  refine ⟨?_, fun f hf g hg => ?_⟩
  · obtain ⟨x, hx, h⟩ := (hsLaw O K Δ L).2.2.1 _ hτ hs0
    exact ⟨Units.mk0 x hx, fun h' => by have := (hN _).1 h'; rw [Units.val_mk0, h] at this; norm_num at this⟩
  have neg : ∀ t : Kˣ, t ∉ NE τ → hs (τ ^ 2 - 4) (t : K) = -1 := fun t ht => by
    have := mt (hN t).2 ht
    unfold hs at this ⊢
    split_ifs at this ⊢ with h
    · exact absurd rfl this
    · rfl
  have out : ∀ x : Kˣ, f (x : Kˣ ⧸ NE τ).out = f x := fun x => by
    have : x⁻¹ * (x : Kˣ ⧸ NE τ).out ∈ NE τ := QuotientGroup.eq.1 (by simp)
    rw [← hf _ this x, mul_comm _ x, mul_inv_cancel_left]
  have hne : ((1 : Kˣ) : Kˣ ⧸ NE τ) ≠ (g : Kˣ ⧸ NE τ) := fun h => hg (by simpa using QuotientGroup.eq.1 h)
  rw [finsum_eq_sum_of_support_subset (s := {((1 : Kˣ) : Kˣ ⧸ NE τ), (g : Kˣ ⧸ NE τ)}) _ fun t _ => ?_, Finset.sum_pair hne, out, out]
  induction t using QuotientGroup.induction_on with
  | H t =>
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases ht : t ∈ NE τ
    · exact .inl (QuotientGroup.eq.2 (by simpa using ht))
    · refine .inr (QuotientGroup.eq.2 ((hN _).2 ?_))
      rw [Units.val_mul, hsMul O K Δ L _ _ _ hτ (Units.ne_zero _) g.ne_zero, neg _ hg, neg _ fun h => ht (by simpa using h)]
      norm_num
