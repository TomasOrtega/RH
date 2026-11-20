import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

/- English proof (translation)
Establish `hex : ∀ t ∈ T, ∃ s, s ∈ T ∧ (t + a) - s ∈ H` using `fun t ht => (hT (t + a) (A.add_mem (hTA t ht) ha)).exists`. Use `choose! φ hφT hφH using hex`. Use `Finset.sum_bij (fun t _ => φ t) (fun t ht => hφT t ht) ?_ ?_ ?_` and prove the remaining obligations. Introduce `t₁ h₁ t₂ h₂ he`. Establish `he' : φ t₁ = φ t₂` using `he`.

Establish `hd : t₁ - t₂ ∈ H`. Use `H.sub_mem (hφH t₁ h₁) (hφH t₂ h₂)` as an intermediate fact. Rewrite `this` using `[he']`. Establish `e : (t₁ + a - φ t₂) - (t₂ + a - φ t₂) = t₁ - t₂` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `h0 : t₁ - t₁ ∈ H` using `by simp [H.zero_mem]`. Conclude with `(hT t₁ (hTA t₁ h₁)).unique ⟨h₁, h0⟩ ⟨h₂, hd⟩`. Introduce `s hs`. Take `⟨t, ⟨ht, hd⟩, -⟩` from `hT (s - a) (A.sub_mem (hTA s hs) ha)`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations.

Establish `h1 : (t + a) - s ∈ H`. Use `H.neg_mem hd` as an intermediate fact. Establish `e : -(s - a - t) = t + a - s` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `h0 : (t + a) - (φ t) ∈ H` using `hφH t ht`.

Establish `hA : t + a ∈ A` using `A.add_mem (hTA t ht) ha`. Conclude with `(hT (t + a) hA).unique ⟨hφT t ht, h0⟩ ⟨hs, h1⟩`. Introduce `t ht`. Use `hF (φ t) _ (hφH t ht)` as an intermediate fact. Establish `e : φ t + (t + a - φ t) = t + a` using `by abel`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem sum_add_eq_sum {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M]
    {A H : AddSubgroup X} {T : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  have hex : ∀ t ∈ T, ∃ s, s ∈ T ∧ (t + a) - s ∈ H := fun t ht =>
    (hT (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! φ hφT hφH using hex
  refine Finset.sum_bij (fun t _ => φ t) (fun t ht => hφT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have he' : φ t₁ = φ t₂ := he
    have hd : t₁ - t₂ ∈ H := by
      have := H.sub_mem (hφH t₁ h₁) (hφH t₂ h₂)
      rw [he'] at this
      have e : (t₁ + a - φ t₂) - (t₂ + a - φ t₂) = t₁ - t₂ := by abel
      rwa [e] at this
    have h0 : t₁ - t₁ ∈ H := by simp [H.zero_mem]
    exact (hT t₁ (hTA t₁ h₁)).unique ⟨h₁, h0⟩ ⟨h₂, hd⟩
  · intro s hs
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := hT (s - a) (A.sub_mem (hTA s hs) ha)
    refine ⟨t, ht, ?_⟩
    have h1 : (t + a) - s ∈ H := by
      have := H.neg_mem hd
      have e : -(s - a - t) = t + a - s := by abel
      rwa [e] at this
    have h0 : (t + a) - (φ t) ∈ H := hφH t ht
    have hA : t + a ∈ A := A.add_mem (hTA t ht) ha
    exact (hT (t + a) hA).unique ⟨hφT t ht, h0⟩ ⟨hs, h1⟩
  · intro t ht
    have := hF (φ t) _ (hφH t ht)
    have e : φ t + (t + a - φ t) = t + a := by abel
    rwa [e] at this

/- English proof (translation)
Establish `h1 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T'.card • ∑ t ∈ T, F t`. Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl (fun t' ht' => sum_add_eq_sum hTA hT F hF (hTA' t' ht')), Finset.sum_const]`. Establish `h2 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T.card • ∑ t ∈ T', F t`. Establish `: ∀ t ∈ T, ∑ t' ∈ T', F (t + t') = ∑ t' ∈ T', F t'` using `fun t ht => by`. Rewrite using `[← sum_add_eq_sum hTA' hT' F hF' (hTA t ht)]`.

Conclude with `Finset.sum_congr rfl (fun t' _ => by rw [add_comm])`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_const]`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← h1, h2]`.
-/
theorem card_smul_sum_eq {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M] [Module ℂ M]
    {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A) {T T' : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hTA' : ∀ t ∈ T', t ∈ A) (hT' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H')
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_comm, Finset.sum_congr rfl
      (fun t' ht' => sum_add_eq_sum hTA hT F hF (hTA' t' ht')), Finset.sum_const]
  have h2 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T.card • ∑ t ∈ T', F t := by
    have : ∀ t ∈ T, ∑ t' ∈ T', F (t + t') = ∑ t' ∈ T', F t' := fun t ht => by
      rw [← sum_add_eq_sum hTA' hT' F hF' (hTA t ht)]
      exact Finset.sum_congr rfl (fun t' _ => by rw [add_comm])
    rw [Finset.sum_congr rfl this, Finset.sum_const]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← h1, h2]

end GlobalTheory.CompanionTheory.Transversal
