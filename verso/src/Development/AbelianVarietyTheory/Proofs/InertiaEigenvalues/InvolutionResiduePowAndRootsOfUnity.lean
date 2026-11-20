import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt

open Polynomial IsLocalRing

namespace GlobalTheory.UnitLemma.InvolRes

/- English proof (translation)
Introduce `S _ _ _ M hM τ hττ hne`. Set `e : S ≃+* S` to `RingEquiv.ofRingHom τ τ (RingHom.ext hττ) (RingHom.ext hττ)`. Set `s` to `ResidueField.mapEquiv e`. Establish `hs : ∀ x, s (residue S x) = residue S (τ x)` using `fun x => rfl`. Take `⟨p, hp⟩` from `CharP.exists (ResidueField S)`.

Use `haveI := hp`. Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField S) p⟩`. Take `⟨-, hsq⟩` from `GlobalTheory.UnitLemma.UnrExt.invol_eq_pow p hM s (fun x => by`. Take `⟨x, rfl⟩` from `residue_surjective x`. Rewrite using `[hs, hs, hττ]) (by`.

Take `⟨x, hx⟩` from `hne`. Conclude with `⟨residue S x, by rw [hs]; exact hx⟩)`. Establish `h1 : ∀ x, residue S (τ x) = residue S x ^ M` using `fun x => by rw [← hs, hsq]`. Use `⟨h1, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hcard2 : 2 ≤ M ^ 2`.

Establish `: 1 < Nat.card (ResidueField S)` using `Finite.one_lt_card`. Use linear arithmetic over natural numbers and integers. Use `set N := M ^ 2 - 1 with hN`. Establish `hNk : (N : ResidueField S) ≠ 0` using `by haveI := Fintype.ofFinite (ResidueField S)`. Establish `h0 : ((N + 1 : ℕ) : ResidueField S) = 0`.

Rewrite using `[show N + 1 = M ^ 2 by omega, ← hM, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]`. Introduce `h`. Simplify using `[h] at h0`. Use `GlobalTheory.UnitLemma.UnrExt.root_unique (residue S) (ker_residue) (X ^ N - 1 : S[X]) (by simpa using X_pow_sub_one_separable_iff.2 hNk) (a := τ w) (b := w ^ M) ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[← map_pow, hw]`.

Simplify using `only [eval_sub, eval_pow, eval_X, eval_one]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hw, one_pow, sub_self]`. Rewrite using `[h1, map_pow]`.
-/
theorem residue_pow_and_roots : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ),
    Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) →
    (∃ x, residue S (τ x) ≠ residue S x) →
    (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  intro S _ _ _ M hM τ hττ hne
  let e : S ≃+* S := RingEquiv.ofRingHom τ τ (RingHom.ext hττ) (RingHom.ext hττ)
  let s := ResidueField.mapEquiv e
  have hs : ∀ x, s (residue S x) = residue S (τ x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  haveI := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField S) p⟩
  obtain ⟨-, hsq⟩ := GlobalTheory.UnitLemma.UnrExt.invol_eq_pow p hM s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hττ]) (by
    obtain ⟨x, hx⟩ := hne
    exact ⟨residue S x, by rw [hs]; exact hx⟩)
  have h1 : ∀ x, residue S (τ x) = residue S x ^ M := fun x => by rw [← hs, hsq]
  refine ⟨h1, fun w hw => ?_⟩
  have hcard2 : 2 ≤ M ^ 2 := by
    have : 1 < Nat.card (ResidueField S) := Finite.one_lt_card
    omega
  set N := M ^ 2 - 1 with hN
  have hNk : (N : ResidueField S) ≠ 0 := by
    haveI := Fintype.ofFinite (ResidueField S)
    have h0 : ((N + 1 : ℕ) : ResidueField S) = 0 := by
      rw [show N + 1 = M ^ 2 by omega, ← hM, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h0
  refine GlobalTheory.UnitLemma.UnrExt.root_unique (residue S) (ker_residue) (X ^ N - 1 : S[X])
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) (a := τ w) (b := w ^ M) ?_ ?_ ?_
  · simp [← map_pow, hw]
  · simp only [eval_sub, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow, sub_self]
  · rw [h1, map_pow]

end GlobalTheory.UnitLemma.InvolRes
