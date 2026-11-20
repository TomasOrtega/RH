import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPthPowerScaleThinShellStatement

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Introduce `L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr`. Take `⟨d, hdF, _hd0, hrx, hx1⟩` from `GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)`. Use `set x := (σ • y - y) * d ^ p with hxdef`. Use `⟨x, Subfield.mem_top x, hx1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Establish `hfix : ∀ j : ℕ, (σ ^ j) • d = d`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]`. Establish `hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p`. Introduce `j`. Rewrite using `[hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]`. Establish `hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero, one_smul, sub_self, zero_mul]`. Establish `hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x)`. Rewrite using `[smul_sub, pow_succ', mul_smul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)` and prove the remaining obligations. Rewrite using `[hv]`. Conclude with `ih`. Establish `hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x)`.

Rewrite using `[Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `h1 : v ((l : L) * x) ≤ r`. Rewrite using `[hlx]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hstep j`. Rewrite `h1` using `[map_mul, GlobalTheory.T.valuation_natCast_eq_one_of_coprime' L v p l hp1 hl, one_mul]`. Conclude with `absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)`.
-/
theorem moves_top_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 →
    (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr
  obtain ⟨d, hdF, _hd0, hrx, hx1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)
  set x := (σ • y - y) * d ^ p with hxdef
  refine ⟨x, Subfield.mem_top x, hx1, ?_⟩
  by_contra hle
  push_neg at hle
  have hfix : ∀ j : ℕ, (σ ^ j) • d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]
  have hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p := by
    intro j
    rw [hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]
  have hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0 := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero,
      one_smul, sub_self, zero_mul]
  have hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x) := by
        rw [smul_sub, pow_succ', mul_smul]; ring
      rw [e]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)
      rw [hv]; exact ih
  have hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : v ((l : L) * x) ≤ r := by
    rw [hlx]
    apply Valuation.map_sum_le
    intro j _
    rw [← Valuation.map_neg, neg_sub]
    exact hstep j
  rw [map_mul, GlobalTheory.T.valuation_natCast_eq_one_of_coprime' L v p l hp1 hl, one_mul] at h1
  exact absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)

end GlobalTheory.AlmostEt
