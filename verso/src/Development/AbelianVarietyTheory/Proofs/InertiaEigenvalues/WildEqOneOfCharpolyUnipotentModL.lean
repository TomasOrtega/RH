import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.WildKill

/- English proof (translation)
Introduce `ha`. Take `⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ)` from `Nat.isCoprime_iff_coprime.2 hab`. Establish `h1 : (u : Ω) * (a : Ω) + (v : Ω) * (b : Ω) = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → Ω) huv`. Establish `hu : ∀ w : ℤ, A.valuation (w : Ω) ≤ 1` using `fun w => (A.valuation_le_one_iff _).2 (intCast_mem A w)`. Establish `h2 : A.valuation ((u : Ω) * (a : Ω) + (v : Ω) * (b : Ω)) < 1`.

Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hu u)) ha`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hu v)) hb`.

Rewrite `h2` using `[h1, map_one]`. Conclude with `lt_irrefl _ h2`.
-/
theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (hab : a.Coprime b)
    (hb : A.valuation (b : Ω) < 1) : ¬ A.valuation (a : Ω) < 1 := by
  intro ha
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (u : Ω) * (a : Ω) + (v : Ω) * (b : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) huv
  have hu : ∀ w : ℤ, A.valuation (w : Ω) ≤ 1 := fun w => (A.valuation_le_one_iff _).2 (intCast_mem A w)
  have h2 : A.valuation ((u : Ω) * (a : Ω) + (v : Ω) * (b : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hu u)) ha
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hu v)) hb
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Establish `: IsGalois E Ω` using `{}`. Set `C : ClosedSubgroup (G E Ω)` to `⟨H, H.isClosed_of_isOpen ho⟩`. Establish `hC : (IntermediateField.fixedField H).fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField C`. Rewrite using `[← hC, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`.

Establish `hy' : (σ ^ n) y = y` using `(IntermediateField.mem_fixedField_iff H y).1 hy _ hH`. Assume the negation of the conclusion as `hne`. Establish `hx : σ y - y ≠ 0` using `sub_ne_zero.2 hne`. Establish `hsum : ∑ i ∈ Finset.range n, (σ ^ i) (σ y - y) = 0`. Establish `: ∀ i, (σ ^ i) (σ y - y) = (σ ^ (i + 1)) y - (σ ^ i) y`.

Introduce `i`. Rewrite using `[map_sub, pow_succ, AlgEquiv.mul_apply]`. Repeatedly rewrite using `[this]`. Rewrite using `[Finset.sum_range_sub (fun i => (σ ^ i) y), hy']`. Simplify using the standard rewrite rules.

Establish `hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) (σ y - y) / (σ y - y) - 1)) < 1` using `Valuation.map_sum_lt _ one_ne_zero fun i _ => GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ _ hx i`. Rewrite `hlt` using `[Finset.sum_sub_distrib, ← Finset.sum_div, hsum]`. Apply `hn` to reduce the goal to its premises. Simplify using `using hlt`.
-/
theorem mem_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (H : Subgroup (G E Ω)) (ho : IsOpen (H : Set (G E Ω))) (σ : G E Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hH : σ ^ n ∈ H) :
    σ ∈ H := by
  have : IsGalois E Ω := {}
  let C : ClosedSubgroup (G E Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hC : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField C
  rw [← hC, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hy' : (σ ^ n) y = y := (IntermediateField.mem_fixedField_iff H y).1 hy _ hH
  by_contra hne
  have hx : σ y - y ≠ 0 := sub_ne_zero.2 hne
  have hsum : ∑ i ∈ Finset.range n, (σ ^ i) (σ y - y) = 0 := by
    have : ∀ i, (σ ^ i) (σ y - y) = (σ ^ (i + 1)) y - (σ ^ i) y := by
      intro i
      rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (σ ^ i) y), hy']
    simp
  have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) (σ y - y) / (σ y - y) - 1)) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i _ =>
      GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ _ hx i
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hlt
  apply hn
  simpa using hlt

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A g l n hg hl hne hA K _ _ rb ho s hs hc`. Use `mem_of_wild A rb.ker ho s (l ^ n) (not_lt_one_of_coprime A (Nat.Coprime.pow_left n ((Nat.coprime_primes hl.out hg.out).2 hne)) hA) hs ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]`. Conclude with `GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ hc`.
-/
theorem eq_one_of_wild_of_unipotent :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g l n : ℕ) [Fact g.Prime] [Fact l.Prime], l ≠ g → A.valuation (g : Ω) < 1 → ∀ (K : Type) [Field K] [CharP K l] (rb : G E Ω →* GL (Fin n) K), IsOpen (rb.ker : Set (G E Ω)) → ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → ((rb s : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n → rb s = 1 := by
  intro E Ω _ _ _ _ _ A g l n hg hl hne hA K _ _ rb ho s hs hc
  refine mem_of_wild A rb.ker ho s (l ^ n)
    (not_lt_one_of_coprime A (Nat.Coprime.pow_left n ((Nat.coprime_primes hl.out hg.out).2 hne)) hA) hs ?_
  rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
  exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ hc

end GlobalTheory.WildKill
