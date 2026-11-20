import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.PolarFlat

/- English proof (translation)
Rewrite using `[← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ j), Finset.sum_powerset_insert (Finset.notMem_erase j _), ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun S hS => ?_` and prove the remaining obligations. Establish `hjS : j ∉ S` using `fun h => Finset.notMem_erase j _ (Finset.mem_powerset.1 hS h)`. Rewrite using `[Finset.card_insert_of_notMem hjS, hg S hjS, pow_succ]`. Simplify using the standard rewrite rules.
-/
theorem altSum_eq_zero {M : Type} [AddCommGroup M] (D : ℕ) (j : Fin D) (g : Finset (Fin D) → M)
    (hg : ∀ S, j ∉ S → g (insert j S) = g S) :
    ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • g S = 0 := by
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ j),
    Finset.sum_powerset_insert (Finset.notMem_erase j _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hjS : j ∉ S := fun h => Finset.notMem_erase j _ (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem hjS, hg S hjS, pow_succ]
  simp

/- English proof (translation)
Use `split_ifs with hf`. Rewrite using `[Finset.sum_eq_single Finset.univ]`. Simplify using the standard rewrite rules. Introduce `S _ hS`. Establish `: ¬ ∀ t, f t ∈ S`.

Introduce `hall`. Apply `hS` to reduce the goal to its premises. Use extensionality with `k`. Take `⟨t, rfl⟩` from `hf k`. Simplify using `[hall t]`.

Simplify using `[this]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [Function.Surjective, not_forall] at hf`. Take `⟨k, hk⟩` from `hf`.

Use `altSum_eq_zero D k _ fun S _ => ?_` and prove the remaining obligations. Establish `: (∀ t, f t ∈ insert k S) ↔ ∀ t, f t ∈ S`. Use `forall_congr' fun t => ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_insert]`. Conclude with `⟨fun h => h.resolve_left fun e => hk ⟨t, e⟩, Or.inr⟩`.

Simplify using `only [this]`.
-/
theorem signCount (D : ℕ) (f : Fin D → Fin D) :
    ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then (1 : ℤ) else 0) =
      if Function.Surjective f then (-1) ^ D else 0 := by
  split_ifs with hf
  · rw [Finset.sum_eq_single Finset.univ]
    · simp
    · intro S _ hS
      have : ¬ ∀ t, f t ∈ S := by
        intro hall
        apply hS
        ext k
        obtain ⟨t, rfl⟩ := hf k
        simp [hall t]
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [Function.Surjective, not_forall] at hf
    obtain ⟨k, hk⟩ := hf
    refine altSum_eq_zero D k _ fun S _ => ?_
    have : (∀ t, f t ∈ insert k S) ↔ ∀ t, f t ∈ S := by
      refine forall_congr' fun t => ?_
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left fun e => hk ⟨t, e⟩, Or.inr⟩
    simp only [this]

/- English proof (translation)
Rewrite using `[← Fin.prod_const, Fintype.prod_sum]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_ite_zero]`. Simplify using the standard rewrite rules.
-/
theorem pow_sum_ite (D : ℕ) (S : Finset (Fin D)) :
    (∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D =
      ∑ f : Fin D → Fin D, if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0 := by
  rw [← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_ite_zero]
  simp

/- English proof (translation)
Repeatedly rewrite using `[pow_sum_ite, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `step : ∀ f : Fin D → Fin D, ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0) = (if Function.Surjective f then ((-1 : ℤ) ^ D) • ∏ k, (X k : MvPolynomial (Fin D) ℝ) else 0)`. Introduce `f`. Establish `e1 : ∀ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0) = (((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then (1 : ℤ) else 0)) • ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ)`.

Apply the tactic sequence `intro S; split_ifs <;> simp`. Repeatedly rewrite using `[e1]`. Rewrite using `[← Finset.sum_smul, signCount]`. Use `split_ifs with hf`. Use `congr 1`.

Conclude with `Equiv.prod_comp (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩) (fun k => (X k : MvPolynomial (Fin D) ℝ))`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[step]`. Rewrite using `[← Finset.sum_filter, Finset.sum_const]`.
-/
theorem polar (D : ℕ) :
    ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • (∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D =
      (Finset.univ.filter fun f : Fin D → Fin D => Function.Surjective f).card •
        (((-1 : ℤ) ^ D) • ∏ k, (X k : MvPolynomial (Fin D) ℝ)) := by
  simp_rw [pow_sum_ite, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ f : Fin D → Fin D, ∑ S : Finset (Fin D),
      ((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0) =
      (if Function.Surjective f then ((-1 : ℤ) ^ D) • ∏ k, (X k : MvPolynomial (Fin D) ℝ) else 0) := by
    intro f
    have e1 : ∀ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) •
        (if ∀ t, f t ∈ S then ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) else 0) =
        (((-1 : ℤ) ^ S.card) • (if ∀ t, f t ∈ S then (1 : ℤ) else 0)) • ∏ t, (X (f t) : MvPolynomial (Fin D) ℝ) := by
      intro S; split_ifs <;> simp
    simp_rw [e1]
    rw [← Finset.sum_smul, signCount]
    split_ifs with hf
    · congr 1
      exact Equiv.prod_comp (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩)
        (fun k => (X k : MvPolynomial (Fin D) ℝ))
    · simp
  simp_rw [step]
  rw [← Finset.sum_filter, Finset.sum_const]

end GlobalTheory.PolarFlat

/- English proof (translation)
Set `e : Finset (Fin D) → Fin D → ℤ` to `fun S i => if i ∈ S then 1 else 0`. Establish `hlin : ∀ S, lin (fun i => ((e S i : ℤ) : ℝ)) = ∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0`. Introduce `S`. Unfold `lin`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hi : i ∈ S <;> simp [e, hi]`. Establish `hB : ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) • Ψ ((∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D) = 0`. Use `GlobalTheory.PolarFlat.altSum_eq_zero D j _ fun S hj => ?_` and prove the remaining obligations. Establish `hu : Function.update (e (insert j S)) j 0 = e S`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `[e, hj]`. Simplify using `[e, hi, Function.update_of_ne hi]`. Rewrite using `[← hlin (insert j S), ← hlin S, h, hu]`.

Establish `hP` using `congrArg Ψ (GlobalTheory.PolarFlat.polar D)`. Rewrite `hP` using `[map_sum]`. Rewrite `hP` using `[map_zsmul]`. Rewrite `hP` using `[hB, map_nsmul, map_zsmul]`. Establish `hcard : (Finset.univ.filter fun f : Fin D → Fin D => Function.Surjective f).card ≠ 0`.

Apply `Finset.card_ne_zero_of_mem (a := id)` to reduce the goal to its premises. Simplify using `[Function.surjective_id]`. Establish `h1` using `(smul_eq_zero.1 hP.symm).resolve_left hcard`. Rewrite `h1` using `[zsmul_eq_mul]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (by simp)`.
-/
theorem GlobalTheory.Div.polar_prod_eq_zero (D : ℕ) (Ψ : MvPolynomial (Fin D) ℝ →ₗ[ℝ] ℝ) (j : Fin D)
    (h : ∀ n : Fin D → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) =
      Ψ (lin (fun i => (Function.update n j 0 i : ℝ)) ^ D)) :
    Ψ (∏ k, MvPolynomial.X k) = 0 := by
  classical
  let e : Finset (Fin D) → Fin D → ℤ := fun S i => if i ∈ S then 1 else 0
  have hlin : ∀ S, lin (fun i => ((e S i : ℤ) : ℝ)) = ∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0 := by
    intro S
    unfold lin
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [e, hi]
  have hB : ∑ S : Finset (Fin D), ((-1 : ℤ) ^ S.card) •
      Ψ ((∑ i, if i ∈ S then (X i : MvPolynomial (Fin D) ℝ) else 0) ^ D) = 0 := by
    refine GlobalTheory.PolarFlat.altSum_eq_zero D j _ fun S hj => ?_
    have hu : Function.update (e (insert j S)) j 0 = e S := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [e, hj]
      · simp [e, hi, Function.update_of_ne hi]
    rw [← hlin (insert j S), ← hlin S, h, hu]
  have hP := congrArg Ψ (GlobalTheory.PolarFlat.polar D)
  rw [map_sum] at hP
  simp_rw [map_zsmul] at hP
  rw [hB, map_nsmul, map_zsmul] at hP
  have hcard : (Finset.univ.filter fun f : Fin D → Fin D => Function.Surjective f).card ≠ 0 := by
    apply Finset.card_ne_zero_of_mem (a := id)
    simp [Function.surjective_id]
  have h1 := (smul_eq_zero.1 hP.symm).resolve_left hcard
  rw [zsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (by simp)
