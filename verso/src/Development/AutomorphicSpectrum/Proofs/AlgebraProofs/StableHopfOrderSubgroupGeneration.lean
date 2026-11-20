import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderIdealsEqTopStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLengthStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGeneratesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProductStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hq N _ _ _ _ AA hst K t ht hgen τ hτ`. Establish `hp1 : 1 < p` using `(Fact.out : p.Prime).one_lt`. Take `⟨⟨S, hS, hSst⟩, -⟩` from `GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hq N AA hst K t ht`. Take `⟨hord, -, hfund, hfunds, -⟩` from `GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hq τ hτ`. Establish `hf0 : f ≠ 0`.

Introduce and unpack `rfl`. Use `Fintype.one_lt_card (α := F)` as an intermediate fact. Rewrite `this` using `[hq, pow_zero]`. Conclude with `lt_irrefl _ this`. Establish `hq1 : 1 < p ^ f` using `Nat.one_lt_pow hf0 hp1`.

Establish `hper1 : τ ^ p ^ f = τ`. Establish `: p ^ f = orderOf τ + 1` using `by omega`. Rewrite using `[this, pow_succ, pow_orderOf_eq_one, one_mul]`. Establish `hper : ∀ m, τ ^ p ^ (f * m) = τ`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hper1]`. Establish `hprin : ∀ χ : MulChar F R, ∃ c : R, c ≠ 0 ∧ xIdeal S.carrier χ = Ideal.span {c}` using `fun χ => (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hq S hSst χ).1`. Use `choose c0 hc0 hc0' using hprin`.

Set `c : ℕ → R` to `fun n => c0 (τ ^ p ^ n)`. Establish `hcX : ∀ n, idealX AA.carrier K t (τ ^ p ^ n) = Ideal.span {c n}`. Introduce `n`. Rewrite using `[idealX, ← hS]`. Conclude with `hc0' _`.

Establish `hom` using `GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hq S hSst τ hτ c (fun n => hc0' _)`. Establish `hcper : ∀ m, c (f * m) = c 0`. Introduce `m`. Simplify using `only [c, hper m, pow_zero, pow_one]`. Set `y : ℕ → NNReal` to `fun n => v (algebraMap R C (c n))`.

Establish `hy1 : ∀ n, y n ≤ 1` using `fun n => hv.map_le_one _`. Establish `hy0 : ∀ n, y n ≠ 0`. Introduce `n`. Use `(Valuation.ne_zero_iff _).2 fun h => hc0 (τ ^ p ^ n) (hv.hom_inj ?_)` and prove the remaining obligations. Simplify `h` using `[c]`.

Establish `hle : ∀ n, y n ^ p ≤ y (n + 1)`. Introduce `n`. Take `⟨δ, hδ⟩` from `(hom n).2.1`. Establish `: y n ^ p = v (algebraMap R C δ) * y (n + 1)`. Simplify using `only [y]`.

Rewrite using `[← map_pow, ← map_pow, hδ, map_mul, map_mul]`. Rewrite using `[this]`. Conclude with `mul_le_of_le_one_left' (hv.map_le_one _)`. Establish `hpowp : ∀ n, (τ ^ p ^ n) ^ p = τ ^ p ^ (n + 1)`. Introduce `n`.

Rewrite using `[← pow_mul, ← pow_succ]`. Establish `hlt : ∀ n, y n ^ p < y (n + 1) → c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1))`. Introduce `n h`. Use `GlobalTheory.T.stable_hopf_order_subgroup_quotient p C v R hv hp F f hq N AA hst K t ht hgen (τ ^ p ^ n) (hfund n) (c n) (c (n + 1)) (hcX n) (by rw [hpowp]; exact hcX (n + 1)) h` as an intermediate fact. Rewrite `this` using `[hpowp]`. Then use the resulting hypothesis.

Establish `heq : ∀ n, y n ^ p = y (n + 1) → c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) → c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1))`. Introduce `n h hg`. Establish `h1` using `GlobalTheory.T.stable_hopf_order_subgroup_length p C v R hv hp F f hq N AA hst K t (τ ^ p ^ n) (c n) hg`. Rewrite `h1` using `[hpowp]`. Take `⟨δ, hδ⟩` from `(hom n).2.1`.

Establish `hv1 : v (algebraMap R C δ) = 1`. Establish `h2 : y n ^ p = v (algebraMap R C δ) * y (n + 1)`. Simplify using `only [y]`. Rewrite using `[← map_pow, ← map_pow, hδ, map_mul, map_mul]`. Rewrite `h2` using `[h]`.

Conclude with `(mul_right_cancel₀ (hy0 (n + 1)) (by rw [one_mul]; exact h2)).symm`. Establish `hu : IsUnit δ`. Use `hv.isUnit_of_one ?_ hv1` and prove the remaining obligations. Use `IsUnit.mk0 _ fun h0 => ?_` and prove the remaining obligations. Rewrite `hv1` using `[h0, map_zero]`.

Conclude with `zero_ne_one hv1`. Rewrite `h1` using `[hδ]`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).1 h1`. Establish `hex : ∃ n, c n ∈ idealD p AA.carrier K t (τ ^ p ^ n)`. Distinguish the cases in `h : ∃ n, y n ^ p < y (n + 1)`.

Take `⟨n, hn⟩` from `h`. Conclude with `⟨n + 1, hlt n hn⟩`. Establish `hall : ∀ n, y n ^ p = y (n + 1)` using `fun n => le_antisymm (hle n) (not_lt.1 fun h' => h ⟨n, h'⟩)`. Establish `hyn : ∀ n, y n = y 0 ^ p ^ n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [← hall n, ih, ← pow_mul, pow_succ]`. Establish `hyf : y 0 ^ p ^ f = y 0`. Rewrite using `[← hyn f]`.

Use `hcper 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Simplify using `only [y, this]`. Establish `hy01 : y 0 = 1`. Use `le_antisymm (hy1 0) (not_lt.1 fun h' => ?_)` and prove the remaining obligations.

Use `pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.2 (hy0 0)) h' hq1` as an intermediate fact. Conclude with `absurd hyf this.ne`. Establish `hu : IsUnit (c 0)`. Use `hv.isUnit_of_one ?_ hy01` and prove the remaining obligations. Use `IsUnit.mk0 _ fun h0 => ?_` and prove the remaining obligations.

Establish `: y 0 = 0` using `by simp only [y, h0, map_zero]`. Conclude with `hy0 0 this`. Establish `hX : idealX AA.carrier K t τ = ⊤`. Use `hcX 0` as an intermediate fact. Rewrite `this` using `[pow_zero, pow_one]`.

Rewrite using `[this]`. Conclude with `Ideal.span_singleton_eq_top.2 hu`. Take `⟨τ', hτ', hD⟩` from `GlobalTheory.T.hopf_order_ideals_eq_top p C v R hv hp F f hq N AA hst K t ht hgen τ hX`. Take `⟨n, -, rfl⟩` from `hfunds τ' hτ'`. Conclude with `⟨n, by rw [hD]; trivial⟩`.

Take `⟨n, hn⟩` from `hex`. Establish `hlater : ∀ k, c (n + k) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + k))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact hn`.

Consider the case `succ k ih`. Break down `(hle (n + k)).lt_or_eq with h | h` into its components or cases. Conclude with `hlt _ h`. Conclude with `heq _ h ih`. Establish `hnf : n ≤ f * n` using `Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hf0)`.

Establish `hg` using `hlater (f * n - n)`. Rewrite `hg` using `[Nat.add_sub_cancel' hnf, hper n]`. Establish `hX` using `hcX (f * n)`. Rewrite `hX` using `[hper n]`. Rewrite using `[hX]`.

Conclude with `(Ideal.span_singleton_le_iff_mem _).2 hg`.
-/
theorem idealX_le_idealD : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hq N _ _ _ _ AA hst K t ht hgen τ hτ
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hq N AA hst K t ht
  obtain ⟨hord, -, hfund, hfunds, -⟩ := GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hq τ hτ
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hq, pow_zero] at this
    exact lt_irrefl _ this
  have hq1 : 1 < p ^ f := Nat.one_lt_pow hf0 hp1
  have hper1 : τ ^ p ^ f = τ := by
    have : p ^ f = orderOf τ + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hper : ∀ m, τ ^ p ^ (f * m) = τ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hper1]
  have hprin : ∀ χ : MulChar F R, ∃ c : R, c ≠ 0 ∧ xIdeal S.carrier χ = Ideal.span {c} :=
    fun χ => (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hq S hSst χ).1
  choose c0 hc0 hc0' using hprin
  let c : ℕ → R := fun n => c0 (τ ^ p ^ n)
  have hcX : ∀ n, idealX AA.carrier K t (τ ^ p ^ n) = Ideal.span {c n} := by
    intro n
    rw [idealX, ← hS]
    exact hc0' _
  have hom := GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hq S hSst τ hτ c (fun n => hc0' _)
  have hcper : ∀ m, c (f * m) = c 0 := by
    intro m
    simp only [c, hper m, pow_zero, pow_one]
  let y : ℕ → NNReal := fun n => v (algebraMap R C (c n))
  have hy1 : ∀ n, y n ≤ 1 := fun n => hv.map_le_one _
  have hy0 : ∀ n, y n ≠ 0 := by
    intro n
    refine (Valuation.ne_zero_iff _).2 fun h => hc0 (τ ^ p ^ n) (hv.hom_inj ?_)
    simpa [c] using h
  have hle : ∀ n, y n ^ p ≤ y (n + 1) := by
    intro n
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
      simp only [y]
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    rw [this]
    exact mul_le_of_le_one_left' (hv.map_le_one _)
  have hpowp : ∀ n, (τ ^ p ^ n) ^ p = τ ^ p ^ (n + 1) := by
    intro n
    rw [← pow_mul, ← pow_succ]
  have hlt : ∀ n, y n ^ p < y (n + 1) → c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h
    have := GlobalTheory.T.stable_hopf_order_subgroup_quotient p C v R hv hp F f hq N AA hst K t ht hgen (τ ^ p ^ n) (hfund n)
      (c n) (c (n + 1)) (hcX n) (by rw [hpowp]; exact hcX (n + 1)) h
    rwa [hpowp] at this
  have heq : ∀ n, y n ^ p = y (n + 1) → c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) →
      c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h hg
    have h1 := GlobalTheory.T.stable_hopf_order_subgroup_length p C v R hv hp F f hq N AA hst K t (τ ^ p ^ n) (c n) hg
    rw [hpowp] at h1
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have hv1 : v (algebraMap R C δ) = 1 := by
      have h2 : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
        simp only [y]
        rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
      rw [h] at h2
      exact (mul_right_cancel₀ (hy0 (n + 1)) (by rw [one_mul]; exact h2)).symm
    have hu : IsUnit δ := by
      refine hv.isUnit_of_one ?_ hv1
      refine IsUnit.mk0 _ fun h0 => ?_
      rw [h0, map_zero] at hv1
      exact zero_ne_one hv1
    rw [hδ] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
  have hex : ∃ n, c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) := by
    by_cases h : ∃ n, y n ^ p < y (n + 1)
    · obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, hlt n hn⟩
    · have hall : ∀ n, y n ^ p = y (n + 1) := fun n =>
        le_antisymm (hle n) (not_lt.1 fun h' => h ⟨n, h'⟩)
      have hyn : ∀ n, y n = y 0 ^ p ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [← hall n, ih, ← pow_mul, pow_succ]
      have hyf : y 0 ^ p ^ f = y 0 := by
        rw [← hyn f]
        have := hcper 1
        rw [mul_one] at this
        simp only [y, this]
      have hy01 : y 0 = 1 := by
        refine le_antisymm (hy1 0) (not_lt.1 fun h' => ?_)
        have := pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.2 (hy0 0)) h' hq1
        exact absurd hyf this.ne
      have hu : IsUnit (c 0) := by
        refine hv.isUnit_of_one ?_ hy01
        refine IsUnit.mk0 _ fun h0 => ?_
        have : y 0 = 0 := by simp only [y, h0, map_zero]
        exact hy0 0 this
      have hX : idealX AA.carrier K t τ = ⊤ := by
        have := hcX 0
        rw [pow_zero, pow_one] at this
        rw [this]
        exact Ideal.span_singleton_eq_top.2 hu
      obtain ⟨τ', hτ', hD⟩ := GlobalTheory.T.hopf_order_ideals_eq_top p C v R hv hp F f hq N AA hst K t ht hgen τ hX
      obtain ⟨n, -, rfl⟩ := hfunds τ' hτ'
      exact ⟨n, by rw [hD]; trivial⟩
  obtain ⟨n, hn⟩ := hex
  have hlater : ∀ k, c (n + k) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + k)) := by
    intro k
    induction k with
    | zero => exact hn
    | succ k ih =>
      rcases (hle (n + k)).lt_or_eq with h | h
      · exact hlt _ h
      · exact heq _ h ih
  have hnf : n ≤ f * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hf0)
  have hg := hlater (f * n - n)
  rw [Nat.add_sub_cancel' hnf, hper n] at hg
  have hX := hcX (f * n)
  rw [hper n] at hX
  rw [hX]
  exact (Ideal.span_singleton_le_iff_mem _).2 hg

end GlobalTheory.CompanionTheory.Ar.GR
