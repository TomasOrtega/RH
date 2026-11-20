import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `B _ _ K τ τ' hle htor`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian τ' : τ'.FG)`. Establish `hrad : K ≤ (τ.colon (s : Set B)).radical`. Introduce `f hf`. Establish `hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ` using `fun b hb => htor b (hs ▸ Submodule.subset_span hb) f hf`.

Use `choose! m hm using hm`. Use `⟨∑ b ∈ s, m b, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_colon]`. Introduce `b hb`. Establish `hb' : b ∈ s` using `hb`.

Establish `hle' : m b ≤ ∑ b ∈ s, m b` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'`. Rewrite using `[smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]`. Conclude with `τ.mul_mem_left _ (hm b hb')`. Take `⟨m, hm⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)`. Establish `hKm : K ^ m * τ' ≤ τ`.

Rewrite using `[Ideal.mul_le]`. Introduce `r hr t ht`. Establish `hr'` using `Submodule.mem_colon.mp (hm hr)`. Rewrite `ht` using `[← hs]`. Proceed by induction on `ht using Submodule.span_induction with`.

Consider the case `mem x hx => simpa [smul_eq_mul] using hr' x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `τ.add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_eq_mul, mul_left_comm]`.

Conclude with `τ.mul_mem_left a hx`. Take `⟨c, hc⟩` from `Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)`. Use `⟨c + m, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hAR : K ^ k ⊓ τ' ≤ τ`. Establish `h` using `hc k (by omega)`.

Simplify using `only [smul_eq_mul, Ideal.mul_top] at h`. Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[inf_comm, sup_inf_assoc_of_le _ hle]`.

Conclude with `sup_le le_rfl hAR`. Conclude with `le_inf hle le_sup_left`.
-/
theorem inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  intro B _ _ K τ τ' hle htor
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian τ' : τ'.FG)
  have hrad : K ≤ (τ.colon (s : Set B)).radical := by
    intro f hf
    have hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ := fun b hb =>
      htor b (hs ▸ Submodule.subset_span hb) f hf
    choose! m hm using hm
    refine ⟨∑ b ∈ s, m b, ?_⟩
    rw [Submodule.mem_colon]
    intro b hb
    have hb' : b ∈ s := hb
    have hle' : m b ≤ ∑ b ∈ s, m b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'
    rw [smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]
    exact τ.mul_mem_left _ (hm b hb')
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)
  have hKm : K ^ m * τ' ≤ τ := by
    rw [Ideal.mul_le]
    intro r hr t ht
    have hr' := Submodule.mem_colon.mp (hm hr)
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem x hx => simpa [smul_eq_mul] using hr' x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact τ.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact τ.mul_mem_left a hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)
  refine ⟨c + m, fun k hk => ?_⟩
  have hAR : K ^ k ⊓ τ' ≤ τ := by
    have h := hc k (by omega)
    simp only [smul_eq_mul, Ideal.mul_top] at h
    rw [h]
    calc K ^ (k - c) * (K ^ c ⊓ τ') ≤ K ^ (k - c) * τ' := Ideal.mul_mono_right inf_le_right
      _ ≤ K ^ m * τ' := Ideal.mul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ ≤ τ := hKm
  apply le_antisymm
  · rw [inf_comm, sup_inf_assoc_of_le _ hle]
    exact sup_le le_rfl hAR
  · exact le_inf hle le_sup_left

end GlobalTheory
