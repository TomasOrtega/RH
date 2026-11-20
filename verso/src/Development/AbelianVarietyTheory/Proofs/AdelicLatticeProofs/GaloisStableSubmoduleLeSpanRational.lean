import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixedStatement

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.GaloisDescent

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `w hw hw0 hcard`. Establish `hrepr0 : b.repr w ≠ 0` using `fun h => hw0 (b.repr.map_eq_zero_iff.mp h)`.

Take `⟨k₀, hk₀⟩` from `Finsupp.support_nonempty_iff.mpr hrepr0`. Establish `hk₀' : b.repr w k₀ ≠ 0` using `Finsupp.mem_support_iff.mp hk₀`. Establish `hvW : (b.repr w k₀)⁻¹ • w ∈ W` using `W.smul_mem _ hw`. Establish `hvk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w) k = (b.repr w k₀)⁻¹ * b.repr w k`. Introduce `k`.

Simplify using the standard rewrite rules. Establish `hv1 : b.repr ((b.repr w k₀)⁻¹ • w) k₀ = 1`. Rewrite using `[hvk, inv_mul_cancel₀ hk₀']`. Distinguish the cases in `hfix : ∀ σ : ℂ ≃+* ℂ, ∀ k, σ (b.repr ((b.repr w k₀)⁻¹ • w) k) = b.repr ((b.repr w k₀)⁻¹ • w) k`. Use `⟨_, hvW, ?_, fun k => GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed _ (fun σ => hfix σ k), ?_⟩` and prove the remaining obligations.

Introduce `h0`. Rewrite `hv1` using `[h0, map_zero, Finsupp.zero_apply]`. Conclude with `zero_ne_one hv1`. Introduce `k hk`. Rewrite `hk`, the goal using `[Finsupp.mem_support_iff]`.

Rewrite `hk` using `[hvk]`. Conclude with `right_ne_zero_of_mul hk`. Use `push Not at hfix`. Take `⟨σ, k₁, hk₁⟩` from `hfix`. Take `⟨v', hv'W, hv'⟩` from `hW σ _ hvW`.

Establish `hdW : (b.repr w k₀)⁻¹ • w - v' ∈ W` using `W.sub_mem hvW hv'W`. Establish `hdk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w - v') k = b.repr ((b.repr w k₀)⁻¹ • w) k - σ (b.repr ((b.repr w k₀)⁻¹ • w) k)`. Introduce `k`. Rewrite using `[map_sub, Finsupp.sub_apply, hv']`. Establish `hd0 : (b.repr w k₀)⁻¹ • w - v' ≠ 0`.

Introduce `h`. Use `hdk k₁` as an intermediate fact. Rewrite `this` using `[h, map_zero, Finsupp.zero_apply]`. Conclude with `hk₁ (sub_eq_zero.mp this.symm).symm`. Establish `hsub : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support ⊆ (b.repr w).support`.

Introduce `k hk`. Rewrite `hk`, the goal using `[Finsupp.mem_support_iff]`. Introduce `hwk`. Apply `hk` to reduce the goal to its premises. Rewrite using `[hdk, hvk, hwk]`.

Simplify using the standard rewrite rules. Establish `hk₀d : k₀ ∉ (b.repr ((b.repr w k₀)⁻¹ • w - v')).support`. Rewrite using `[Finsupp.mem_support_iff, not_not, hdk, hv1, map_one, sub_self]`. Establish `hlt : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support.card < n`. Rewrite using `[← hcard]`.

Conclude with `Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k₀, hk₀, hk₀d⟩)`. Take `⟨u, huW, hu0, hurat, husub⟩` from `ih _ hlt _ hdW hd0 rfl`. Conclude with `⟨u, huW, hu0, hurat, husub.trans hsub⟩`.
-/
private theorem exists_rational_support_subset_of_galois_stable {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hw0 hcard
  have hrepr0 : b.repr w ≠ 0 := fun h => hw0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k₀, hk₀⟩ := Finsupp.support_nonempty_iff.mpr hrepr0
  have hk₀' : b.repr w k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀

  have hvW : (b.repr w k₀)⁻¹ • w ∈ W := W.smul_mem _ hw
  have hvk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w) k = (b.repr w k₀)⁻¹ * b.repr w k := by
    intro k; simp
  have hv1 : b.repr ((b.repr w k₀)⁻¹ • w) k₀ = 1 := by
    rw [hvk, inv_mul_cancel₀ hk₀']
  by_cases hfix : ∀ σ : ℂ ≃+* ℂ, ∀ k,
      σ (b.repr ((b.repr w k₀)⁻¹ • w) k) = b.repr ((b.repr w k₀)⁻¹ • w) k
  ·
    refine ⟨_, hvW, ?_, fun k => GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed _ (fun σ => hfix σ k), ?_⟩
    · intro h0
      rw [h0, map_zero, Finsupp.zero_apply] at hv1
      exact zero_ne_one hv1
    · intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [hvk] at hk
      exact right_ne_zero_of_mul hk
  ·
    push Not at hfix
    obtain ⟨σ, k₁, hk₁⟩ := hfix
    obtain ⟨v', hv'W, hv'⟩ := hW σ _ hvW
    have hdW : (b.repr w k₀)⁻¹ • w - v' ∈ W := W.sub_mem hvW hv'W
    have hdk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w - v') k =
        b.repr ((b.repr w k₀)⁻¹ • w) k - σ (b.repr ((b.repr w k₀)⁻¹ • w) k) := by
      intro k; rw [map_sub, Finsupp.sub_apply, hv']
    have hd0 : (b.repr w k₀)⁻¹ • w - v' ≠ 0 := by
      intro h
      have := hdk k₁
      rw [h, map_zero, Finsupp.zero_apply] at this
      exact hk₁ (sub_eq_zero.mp this.symm).symm
    have hsub : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support ⊆ (b.repr w).support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      intro hwk
      apply hk
      rw [hdk, hvk, hwk]
      simp
    have hk₀d : k₀ ∉ (b.repr ((b.repr w k₀)⁻¹ • w - v')).support := by
      rw [Finsupp.mem_support_iff, not_not, hdk, hv1, map_one, sub_self]
    have hlt : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k₀, hk₀, hk₀d⟩)
    obtain ⟨u, huW, hu0, hurat, husub⟩ := ih _ hlt _ hdW hd0 rfl
    exact ⟨u, huW, hu0, hurat, husub.trans hsub⟩

/- English proof (translation)
Introduce `w hw hw0 hcard` and use `exists_rational_support_subset_of_galois_stable b W hW n w hw hw0 hcard`.
-/
theorem exists_rational_support_subset {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) (n : ℕ) :
    ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support :=
  fun w hw hw0 hcard => exists_rational_support_subset_of_galois_stable b W hW n w hw hw0 hcard

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `w hw hcard`. Distinguish the cases in `hw0 : w = 0`.

Rewrite using `[hw0]`. Conclude with `Submodule.zero_mem _`. Take `⟨u, huW, hu0, hurat, husub⟩` from `exists_rational_support_subset b W hW n w hw hw0 hcard`. Establish `hru : b.repr u ≠ 0` using `fun h => hu0 (b.repr.map_eq_zero_iff.mp h)`. Take `⟨k, hk⟩` from `Finsupp.support_nonempty_iff.mpr hru`.

Establish `huk : b.repr u k ≠ 0` using `Finsupp.mem_support_iff.mp hk`. Establish `hdk : ∀ j, b.repr (w - (b.repr w k / b.repr u k) • u) j = b.repr w j - (b.repr w k / b.repr u k) * b.repr u j`. Introduce `j`. Simplify using the standard rewrite rules. Establish `hsub : (b.repr (w - (b.repr w k / b.repr u k) • u)).support ⊆ (b.repr w).support`.

Introduce `j hj`. Rewrite `hj`, the goal using `[Finsupp.mem_support_iff]`. Introduce `hwj`. Apply `hj` to reduce the goal to its premises. Establish `huj : b.repr u j = 0`.

Assume the negation of the conclusion as `h`. Conclude with `Finsupp.mem_support_iff.mp (husub (Finsupp.mem_support_iff.mpr h)) hwj`. Rewrite using `[hdk, hwj, huj]`. Simplify using the standard rewrite rules. Establish `hkout : k ∉ (b.repr (w - (b.repr w k / b.repr u k) • u)).support`.

Rewrite using `[Finsupp.mem_support_iff, not_not, hdk, div_mul_cancel₀ _ huk, sub_self]`. Establish `hlt : (b.repr (w - (b.repr w k / b.repr u k) • u)).support.card < n`. Rewrite using `[← hcard]`. Conclude with `Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, husub hk, hkout⟩)`. Establish `h1` using `ih _ hlt _ (W.sub_mem hw (W.smul_mem _ huW)) rfl`.

Establish `h2 : u ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q}` using `Submodule.subset_span ⟨huW, hurat⟩`. Establish `h3` using `Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w k / b.repr u k) h2)`. Rewrite `h3` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
private theorem mem_span_rational_of_galois_stable_of_support_card {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, (b.repr w).support.card = n →
      w ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hcard
  by_cases hw0 : w = 0
  · rw [hw0]; exact Submodule.zero_mem _
  obtain ⟨u, huW, hu0, hurat, husub⟩ :=
    exists_rational_support_subset b W hW n w hw hw0 hcard
  have hru : b.repr u ≠ 0 := fun h => hu0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hru
  have huk : b.repr u k ≠ 0 := Finsupp.mem_support_iff.mp hk

  have hdk : ∀ j, b.repr (w - (b.repr w k / b.repr u k) • u) j =
      b.repr w j - (b.repr w k / b.repr u k) * b.repr u j := by
    intro j; simp
  have hsub : (b.repr (w - (b.repr w k / b.repr u k) • u)).support ⊆ (b.repr w).support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    intro hwj
    apply hj
    have huj : b.repr u j = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (husub (Finsupp.mem_support_iff.mpr h)) hwj
    rw [hdk, hwj, huj]
    simp
  have hkout : k ∉ (b.repr (w - (b.repr w k / b.repr u k) • u)).support := by
    rw [Finsupp.mem_support_iff, not_not, hdk, div_mul_cancel₀ _ huk, sub_self]
  have hlt : (b.repr (w - (b.repr w k / b.repr u k) • u)).support.card < n := by
    rw [← hcard]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, husub hk, hkout⟩)
  have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ huW)) rfl
  have h2 : u ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} :=
    Submodule.subset_span ⟨huW, hurat⟩
  have h3 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w k / b.repr u k) h2)
  rwa [sub_add_cancel] at h3

/- English proof (translation)
Introduce `V κ _ _ b W hW w hw`. Conclude with `mem_span_rational_of_galois_stable_of_support_card b W hW _ w hw rfl`.
-/
theorem le_span_rational :
    ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro V κ _ _ b W hW w hw
  exact mem_span_rational_of_galois_stable_of_support_card b W hW _ w hw rfl

end GlobalTheory.ClassFin.GaloisDescent
