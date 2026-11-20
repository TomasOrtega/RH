import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `V G _ _ _ ρ B D hD hadd hsmul hinv K y hy hfin`. Use `set s := hfin.toFinset with hs`. Establish `hmem : ∀ x, x ∈ s ↔ ∃ k ∈ K, ρ k y = x` using `fun x => by`. Rewrite using `[hs, Set.Finite.mem_toFinset]`. Both sides reduce to the same expression.

Establish `hcomp : ∀ g h x, ρ g (ρ h x) = ρ (g * h) x` using `fun g h x => by rw [map_mul]; rfl`. Establish `hone : ∀ x, ρ 1 x = x` using `fun x => by rw [map_one]; rfl`. Establish `hys : y ∈ s` using `(hmem y).2 ⟨1, K.one_mem, hone y⟩`. Establish `hn : (s.card : ℂ) ≠ 0` using `by exact_mod_cast (Finset.card_pos.2 ⟨y, hys⟩).ne'`. Establish `hsD : ∀ x ∈ s, x ∈ D`.

Introduce `x hx`. Take `⟨k, -, rfl⟩` from `(hmem x).1 hx`. Conclude with `hD k y hy`. Use `⟨(s.card : ℂ)⁻¹ • ∑ x ∈ s, x, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x hx => Submodule.subset_span ((hmem x).1 hx))`.

Introduce `k hk`. Rewrite using `[map_smul, map_sum]`. Use `congr 1`. Apply `Finset.sum_nbij' (ρ k) (ρ k⁻¹)` to reduce the goal to its premises. Introduce `a ha`.

Take `⟨k', hk', rfl⟩` from `(hmem a).1 ha`. Conclude with `(hmem _).2 ⟨k * k', K.mul_mem hk hk', (hcomp k k' y).symm⟩`. Introduce `a ha`. Take `⟨k', hk', rfl⟩` from `(hmem a).1 ha`. Conclude with `(hmem _).2 ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', (hcomp _ _ y).symm⟩`.

Introduce `a _`. Rewrite using `[hcomp, inv_mul_cancel, hone]`. Introduce `a _`. Rewrite using `[hcomp, mul_inv_cancel, hone]`. Introduce `a _`.

Both sides reduce to the same expression. Introduce `v hv hfix`. Establish `key : ∀ t : Finset V, (∀ x ∈ t, x ∈ D) → (∑ x ∈ t, x) ∈ D ∧ B (∑ x ∈ t, x) v = ∑ x ∈ t, B x v`. Introduce `t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations.

Introduce `_`. Use `⟨by simpa using D.zero_mem, ?_⟩` and prove the remaining obligations. Establish `h0` using `hsmul 0 0 D.zero_mem v hv`. Simplify using `using h0`. Introduce `a t ha ih hall`.

Establish `haD` using `hall a (Finset.mem_insert_self a t)`. Establish `ih'` using `ih (fun x hx => hall x (Finset.mem_insert_of_mem hx))`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `⟨D.add_mem haD ih'.1, by rw [hadd a haD _ ih'.1 v hv, ih'.2]⟩`. Take `⟨hsumD, hsumB⟩` from `key s hsD`.

Rewrite using `[hsmul _ _ hsumD v hv, hsumB]`. Establish `hterm : ∀ x ∈ s, B x v = B y v`. Introduce `x hx`. Take `⟨k, hk, rfl⟩` from `(hmem x).1 hx`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]`.
-/
theorem orbit_average_fixed_same_pairing : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ g, ∀ x ∈ D, ρ g x ∈ D) →
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y) →
    ∀ (K : Subgroup G), ∀ y ∈ D, {x | ∃ k ∈ K, ρ k y = x}.Finite →
    ∃ e ∈ Submodule.span ℂ {x | ∃ k ∈ K, ρ k y = x}, (∀ k ∈ K, ρ k e = e) ∧
      ∀ v ∈ D, (∀ k ∈ K, ρ k v = v) → B e v = B y v := by
  intro V G _ _ _ ρ B D hD hadd hsmul hinv K y hy hfin
  classical
  set s := hfin.toFinset with hs
  have hmem : ∀ x, x ∈ s ↔ ∃ k ∈ K, ρ k y = x := fun x => by
    rw [hs, Set.Finite.mem_toFinset]; rfl
  have hcomp : ∀ g h x, ρ g (ρ h x) = ρ (g * h) x := fun g h x => by rw [map_mul]; rfl
  have hone : ∀ x, ρ 1 x = x := fun x => by rw [map_one]; rfl
  have hys : y ∈ s := (hmem y).2 ⟨1, K.one_mem, hone y⟩
  have hn : (s.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 ⟨y, hys⟩).ne'
  have hsD : ∀ x ∈ s, x ∈ D := by
    intro x hx; obtain ⟨k, -, rfl⟩ := (hmem x).1 hx; exact hD k y hy
  refine ⟨(s.card : ℂ)⁻¹ • ∑ x ∈ s, x, ?_, ?_, ?_⟩
  · exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun x hx => Submodule.subset_span ((hmem x).1 hx))
  · intro k hk
    rw [map_smul, map_sum]
    congr 1
    apply Finset.sum_nbij' (ρ k) (ρ k⁻¹)
    · intro a ha
      obtain ⟨k', hk', rfl⟩ := (hmem a).1 ha
      exact (hmem _).2 ⟨k * k', K.mul_mem hk hk', (hcomp k k' y).symm⟩
    · intro a ha
      obtain ⟨k', hk', rfl⟩ := (hmem a).1 ha
      exact (hmem _).2 ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', (hcomp _ _ y).symm⟩
    · intro a _; rw [hcomp, inv_mul_cancel, hone]
    · intro a _; rw [hcomp, mul_inv_cancel, hone]
    · intro a _; rfl
  · intro v hv hfix
    have key : ∀ t : Finset V, (∀ x ∈ t, x ∈ D) →
        (∑ x ∈ t, x) ∈ D ∧ B (∑ x ∈ t, x) v = ∑ x ∈ t, B x v := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        refine ⟨by simpa using D.zero_mem, ?_⟩
        have h0 := hsmul 0 0 D.zero_mem v hv
        simpa using h0
      · intro a t ha ih hall
        have haD := hall a (Finset.mem_insert_self a t)
        have ih' := ih (fun x hx => hall x (Finset.mem_insert_of_mem hx))
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact ⟨D.add_mem haD ih'.1, by rw [hadd a haD _ ih'.1 v hv, ih'.2]⟩
    obtain ⟨hsumD, hsumB⟩ := key s hsD
    rw [hsmul _ _ hsumD v hv, hsumB]
    have hterm : ∀ x ∈ s, B x v = B y v := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := (hmem x).1 hx
      calc B (ρ k y) v = B (ρ k y) (ρ k v) := by rw [hfix k hk]
        _ = B y v := hinv k y hy v hv
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul]

end GlobalTheory
