import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

/- English proof (translation)
Establish `h1 : ∏ a, ∏ b, g a b = ∏ p : Fin n × Fin n, g p.1 p.2` using `(Fintype.prod_prod_type' (f := g)).symm`. Establish `hd : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => p.1 = p.2), g p.1 p.2 = ∏ a, g a a`. Use `Finset.prod_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p _`. Conclude with `mem_univ _`.

Introduce `a _`. Simplify using the standard rewrite rules. Introduce `p hp`. Establish `: p.1 = p.2` using `(mem_filter.mp hp).2`. Apply the tactic sequence `ext <;> simp [this]`.

Introduce `a _`. Both sides reduce to the same expression. Introduce `p hp`. Establish `: p.1 = p.2` using `(mem_filter.mp hp).2`. Simplify using `[← this]`.

Establish `ho : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => ¬ p.1 = p.2), g p.1 p.2 = ∏ p ∈ prs n, g p.1 p.2`. Use `Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [mem_filter, mem_univ, true_and] at hp`. Simplify using `only [prs, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]`.

Conclude with `lt_of_le_of_ne (not_lt.mp hp.1) (Ne.symm hp.2)`. Introduce `p hp`. Establish `hlt : p.1 < p.2` using `by simpa [prs] using hp`. Simplify using `only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]`. Conclude with `⟨not_lt.mpr hlt.le, hlt.ne'⟩`.

Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`.

Simplify using `using hg p.1 p.2`. Rewrite using `[h1, ← Finset.prod_filter_mul_prod_filter_not univ (fun p : Fin n × Fin n => p.1 < p.2), ← Finset.prod_filter_mul_prod_filter_not (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2) (fun p => p.1 = p.2), hd, ho]`. Express the relevant statement in the definitionally equal form `(∏ p ∈ prs n, g p.1 p.2) * _ = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_prod_symm_eq_diag_mul_prs_sq {n : ℕ} (g : Fin n → Fin n → ℂ) (hg : ∀ a b, g a b = g b a) :
    ∏ a, ∏ b, g a b = (∏ a, g a a) * (∏ p ∈ prs n, g p.1 p.2) ^ 2 := by
  have h1 : ∏ a, ∏ b, g a b = ∏ p : Fin n × Fin n, g p.1 p.2 :=
    (Fintype.prod_prod_type' (f := g)).symm
  have hd : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => p.1 = p.2),
      g p.1 p.2 = ∏ a, g a a := by
    refine Finset.prod_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro a _; simp
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      ext <;> simp [this]
    · intro a _; rfl
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      simp [← this]
  have ho : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => ¬ p.1 = p.2),
      g p.1 p.2 = ∏ p ∈ prs n, g p.1 p.2 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [prs, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hp.1) (Ne.symm hp.2)
    · intro p hp
      have hlt : p.1 < p.2 := by simpa [prs] using hp
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨not_lt.mpr hlt.le, hlt.ne'⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simpa using hg p.1 p.2
  rw [h1, ← Finset.prod_filter_mul_prod_filter_not univ (fun p : Fin n × Fin n => p.1 < p.2),
    ← Finset.prod_filter_mul_prod_filter_not (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2)
      (fun p => p.1 = p.2), hd, ho]
  change (∏ p ∈ prs n, g p.1 p.2) * _ = _
  ring

/- English proof (translation)
Establish `hZ : (∏ a, z a) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun a _ => hz a`. Establish `h1 : ∏ a, ∏ b, (1 + z a / z b) = (∏ a, ∏ b, (z a + z b)) / (∏ a, z a) ^ n`. Establish `hterm : ∀ a b, 1 + z a / z b = (z a + z b) / z b`. Introduce `a b`. Clear denominators, using `[hz b]` for the nonvanishing conditions.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hterm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `h2 : ∏ a, ∏ b, (z a + z b) = 2 ^ n * (∏ a, z a) * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2`. Rewrite using `[prod_prod_symm_eq_diag_mul_prs_sq (fun a b => z a + z b) (fun a b => add_comm _ _)]`. Establish `: ∏ a, (z a + z a) = 2 ^ n * ∏ a, z a`.

Simplify using `only [← two_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[this]`. Establish `h3 : (∏ a, z a) * (∏ a, z a) ^ (n - 1) = (∏ a, z a) ^ n`. Break down `n with _ | m` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `[pow_succ, mul_comm]`. Rewrite using `[h1, h2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_comm (∏ a, z a), ← h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_one_add_div_mul_prod_pow {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a ≠ 0) :
    (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1)
      = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  have hZ : (∏ a, z a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hz a
  have h1 : ∏ a, ∏ b, (1 + z a / z b) = (∏ a, ∏ b, (z a + z b)) / (∏ a, z a) ^ n := by
    have hterm : ∀ a b, 1 + z a / z b = (z a + z b) / z b := by
      intro a b
      field_simp [hz b]
      ring
    simp only [hterm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h2 : ∏ a, ∏ b, (z a + z b) = 2 ^ n * (∏ a, z a) * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
    rw [prod_prod_symm_eq_diag_mul_prs_sq (fun a b => z a + z b) (fun a b => add_comm _ _)]
    have : ∏ a, (z a + z a) = 2 ^ n * ∏ a, z a := by
      simp only [← two_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [this]
  have h3 : (∏ a, z a) * (∏ a, z a) ^ (n - 1) = (∏ a, z a) ^ n := by
    rcases n with _ | m
    · simp
    · simp [pow_succ, mul_comm]
  rw [h1, h2]
  field_simp
  rw [mul_comm (∏ a, z a), ← h3]
  ring

end GlobalTheory.CompanionTheory.CoefId
