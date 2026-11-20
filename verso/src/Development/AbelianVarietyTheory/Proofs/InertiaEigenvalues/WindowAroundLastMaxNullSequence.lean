import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `β c h hc hβ0 hne hlim`. Establish `hfin : ∀ ε : ℝ, 0 < ε → {k | ε ≤ β k}.Finite`. Introduce `ε hε`. Establish `h1 : ∀ᶠ k in Filter.cofinite, β k < ε` using `hlim.eventually (gt_mem_nhds hε)`. Rewrite `h1` using `[Filter.eventually_cofinite]`.

Simplify `h1` using `[not_lt]`. Take `⟨k₀, hk₀⟩` from `hne`. Establish `hpos : 0 < β k₀` using `lt_of_le_of_ne (hβ0 k₀) (Ne.symm hk₀)`. Use `set T := (hfin _ hpos).toFinset with hT`. Establish `hk₀T : k₀ ∈ T` using `by simp [T]`.

Take `⟨m, hmT, hm⟩` from `T.exists_max_image β ⟨k₀, hk₀T⟩`. Establish `hmax : ∀ k, β k ≤ β m`. Introduce `k`. Distinguish the cases in `hk : β k₀ ≤ β k`. Conclude with `hm k (by simp [T, hk])`.

Use `push_neg at hk`. Establish `: β k₀ ≤ β m` using `hm k₀ hk₀T`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set U := T.filter (fun k => β k = β m) with hU`. Establish `hmU : m ∈ U` using `Finset.mem_filter.2 ⟨hmT, rfl⟩`.

Use `set N := U.max' ⟨m, hmU⟩ with hNdef`. Establish `hNU : N ∈ U` using `U.max'_mem _`. Establish `hN : β N = β m` using `(Finset.mem_filter.1 hNU).2`. Establish `hk₀m : β k₀ ≤ β m` using `hm k₀ hk₀T`. Establish `hNlast : ∀ k, N < k → β k < β N`.

Introduce `k hk`. Break down `lt_or_eq_of_le (hmax k) with h1 | h1` into its components or cases. Rewrite using `[hN]`. Conclude with `h1`. It suffices to derive a contradiction.

Establish `hkU : k ∈ U`. Use `Finset.mem_filter.2 ⟨?_, h1⟩` and prove the remaining obligations. Simplify using `[T]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `U.le_max' k hkU` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hc₀ : 0 < β N` using `by rw [hN]; linarith`. Establish `hcpos : 0 < c * β N` using `mul_pos hc hc₀`. Use `set F := (hfin _ hcpos).toFinset with hF`. Use `set B : ℕ := (F.image (fun k => k.natAbs)).sup id ⊔ N.natAbs with hB`.

Establish `hNB : N.natAbs ≤ B` using `le_sup_right`. Establish `hFB : ∀ k, c * β N ≤ β k → k.natAbs ≤ B`. Introduce `k hk`. Establish `hkF : k ∈ F` using `by simp [F, hk]`. Establish `: k.natAbs ≤ (F.image (fun k => k.natAbs)).sup id` using `Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hkF)`.

Conclude with `le_trans this le_sup_left`. Use `⟨B + h, B + h + B, (N + B).toNat, ?_⟩` and prove the remaining obligations. Establish `hx : ((((N + (B : ℤ)).toNat + h : ℕ)) : ℤ) - ((B + h : ℕ) : ℤ) = N` using `by omega`. Rewrite using `[hx]`. Use `⟨by omega, by omega, hc₀, fun k => hN ▸ hmax k, fun k hk => hNlast k hk, ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `hFB k hlt.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem window_around_last_max : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  intro β c h hc hβ0 hne hlim
  have hfin : ∀ ε : ℝ, 0 < ε → {k | ε ≤ β k}.Finite := by
    intro ε hε
    have h1 : ∀ᶠ k in Filter.cofinite, β k < ε := hlim.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at h1
    simpa [not_lt] using h1
  obtain ⟨k₀, hk₀⟩ := hne
  have hpos : 0 < β k₀ := lt_of_le_of_ne (hβ0 k₀) (Ne.symm hk₀)
  set T := (hfin _ hpos).toFinset with hT
  have hk₀T : k₀ ∈ T := by simp [T]
  obtain ⟨m, hmT, hm⟩ := T.exists_max_image β ⟨k₀, hk₀T⟩
  have hmax : ∀ k, β k ≤ β m := by
    intro k
    by_cases hk : β k₀ ≤ β k
    · exact hm k (by simp [T, hk])
    · push_neg at hk
      have : β k₀ ≤ β m := hm k₀ hk₀T
      linarith
  set U := T.filter (fun k => β k = β m) with hU
  have hmU : m ∈ U := Finset.mem_filter.2 ⟨hmT, rfl⟩
  set N := U.max' ⟨m, hmU⟩ with hNdef
  have hNU : N ∈ U := U.max'_mem _
  have hN : β N = β m := (Finset.mem_filter.1 hNU).2
  have hk₀m : β k₀ ≤ β m := hm k₀ hk₀T
  have hNlast : ∀ k, N < k → β k < β N := by
    intro k hk
    rcases lt_or_eq_of_le (hmax k) with h1 | h1
    · rw [hN]; exact h1
    · exfalso
      have hkU : k ∈ U := by
        refine Finset.mem_filter.2 ⟨?_, h1⟩
        simp [T]; linarith
      have := U.le_max' k hkU
      omega
  have hc₀ : 0 < β N := by rw [hN]; linarith
  have hcpos : 0 < c * β N := mul_pos hc hc₀
  set F := (hfin _ hcpos).toFinset with hF
  set B : ℕ := (F.image (fun k => k.natAbs)).sup id ⊔ N.natAbs with hB
  have hNB : N.natAbs ≤ B := le_sup_right
  have hFB : ∀ k, c * β N ≤ β k → k.natAbs ≤ B := by
    intro k hk
    have hkF : k ∈ F := by simp [F, hk]
    have : k.natAbs ≤ (F.image (fun k => k.natAbs)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hkF)
    exact le_trans this le_sup_left
  refine ⟨B + h, B + h + B, (N + B).toNat, ?_⟩
  have hx : ((((N + (B : ℤ)).toNat + h : ℕ)) : ℤ) - ((B + h : ℕ) : ℤ) = N := by omega
  rw [hx]
  refine ⟨by omega, by omega, hc₀, fun k => hN ▸ hmax k, fun k hk => hNlast k hk, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  have := hFB k hlt.le
  omega

end GlobalTheory
