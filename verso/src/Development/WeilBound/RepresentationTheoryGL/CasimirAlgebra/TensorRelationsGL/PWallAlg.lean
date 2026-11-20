import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlgA

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

open WallAlgP in
/- English proof (translation)
Unfold `WallAlg`. Introduce `n M _ _ E₁ E₂ h₁ h₂ hcomm s₁ s₂ c hc₁ hc₂ m X hX hperm hOm htot`. Take `⟨ξ0, hξ0X, hξ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hX`. Establish `eqA : (n:ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c`. Establish `tr₁` using `(hQ n M E₁ h₁).2.2.1 _ hc₁`.

Establish `tr₂` using `(hQ n M E₂ h₂).2.2.1 _ hc₂`. Establish `key1` using `trace_rel E₁ E₂ c _ _ ξ0 tr₁ tr₂ (fun a b => htot a b ξ0 hξ0X)`. Establish `e` using `smul_left_injective ℂ hξ0 key1`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e`. Take the linear combination `e`.

Use `⟨eqA, fun hm => ?_⟩` and prove the remaining obligations. Establish `hOmC : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m), pm σ * Om E₁ p = Om E₁ (σ p) * pm σ` using `(hA n M (Fin m) E₁ h₁ Finset.univ).2.2.2`. Establish `key : ∀ k, k < n → k ≤ m → (∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0) → k < m ∧ ∃ ξ ∈ X, alt (firstG m (k + 1)) ξ ≠ 0`. Introduce `k hkn hkm hPk`. Assume the negation of the conclusion as `hneg`.

Establish `hout : ∀ ξ ∈ X, ∀ i : Fin m, k ≤ (i:ℕ) → ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) = alt (firstG m k) ξ`. Introduce `ξ hξ i hi`. Establish `hk : k < m` using `lt_of_le_of_lt hi i.isLt`. Establish `hz : ∀ η ∈ X, alt (firstG m (k + 1)) η = 0`. Introduce `η hη`.

Assume the negation of the conclusion as `hne`. Conclude with `hneg ⟨hk, η, hη, hne⟩`. Conclude with `outer hk X hperm hz ξ hξ i hi`. Establish `hsw : ∀ ξ : TV n M (Fin m), ∀ i j : Fin m, i ≠ j → (i:ℕ) < k → (j:ℕ) < k → pm (Equiv.swap i j) (alt (firstG m k) ξ) = -alt (firstG m k) ξ`. Introduce `ξ i j hij hi hj`.

Establish `hmem : Equiv.swap i j ∈ firstG m k`. Rewrite using `[mem_firstG]`. Introduce `l hl`. Apply `Equiv.swap_apply_of_ne_of_ne` to reduce the goal to its premises. Introduce `h`.

Rewrite `hl` using `[h]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Rewrite `hl` using `[h]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[pm_alt_first _ hmem, Equiv.Perm.sign_swap hij]`. Simplify using the standard rewrite rules. Establish `hinv : ∀ y ∈ X.map (alt (firstG m k)), (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₁ j) y ∈ X.map (alt (firstG m k))`. Introduce `y hy`. Take `⟨ξ, hξ, rfl⟩` from `Submodule.mem_map.mp hy`.

Simplify using `only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]`. Use `Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j hj => Submodule.sum_mem _ fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[← om_alt E₁ hOmC k ξ]`. Conclude with `Submodule.mem_map_of_mem (Submodule.sum_mem _ fun j _ => hOm j ξ hξ)`. Establish `hi'` using `(Finset.mem_filter.mp hi).2`.

Establish `hj'` using `(Finset.mem_filter.mp hj).2`. Rewrite using `[hsw ξ i j (ne_of_lt hi') (lt_trans (show (i:ℕ) < (j:ℕ) from hi') hj') hj']`. Conclude with `Submodule.neg_mem _ (Submodule.mem_map_of_mem hξ)`. Take `⟨ξ1, hξ1X, hξ1⟩` from `hPk`. Take `⟨L₁, hL₁⟩` from `(hS n M E₁ h₁ (fun _ => s₁) s₁ hc₁ (fun _ => ⟨0, by simp⟩) m).1 k hkm`.

Take `⟨L₂, hL₂⟩` from `(hS n M E₂ h₂ (fun _ => s₂) s₂ hc₂ (fun _ => ⟨0, by simp⟩) m).1 k hkm`. Take `⟨w, hwY, hw0, r₁, hw1⟩` from `eigen (X.map (alt (firstG m k))) _ hinv (fun r : ℕ => (k:ℂ) * s₁ + r) L₁ hL₁ (alt (firstG m k) ξ1) (Submodule.mem_map_of_mem hξ1X) hξ1`. Take `⟨ζ, hζ, rfl⟩` from `Submodule.mem_map.mp hwY`. Establish `hwX : alt (firstG m k) ζ ∈ X` using `alt_mem X hperm ζ hζ`. Establish `hw` using `fun a b => htot a b _ hwX`.

Use `set w := alt (firstG m k) ζ with hwdef`. Establish `hT : ∀ E : Fin n → Fin n → Module.End ℂ M, (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E j) w = ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), Om E j w + ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j …`. Introduce `E`. Simplify using `only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]`. Establish `hsplit : ∀ j : Fin m, (j:ℕ) < k → ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w = ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w + ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w`.

Introduce `j hj`. Rewrite using `[Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : p = j`. Substitute `h1` using the available equality.

Simplify using `[not_le.mpr hj]`. Distinguish the cases in `h2 : (p:ℕ) < k`. Simplify using `[h1, h2, not_le.mpr h2]`. Simplify using `[h1, h2, not_lt.mp h2]`. Establish `e1 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w = ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), (∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w + ∑ …` using `Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_filter.mp hj).2`.

Establish `e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j p) w = ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), w` using `Finset.sum_congr rfl fun p hp => hout ζ hζ p (Finset.mem_filter.mp hp).2`. Establish `e3 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w = 2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w` using `symm_sum (fun i j => pm (Equiv.swap i j) w) (fun i j => by simp only [Equiv.swap_comm i j])`. Establish `hmid : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w = 2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w + ((m:ℂ) - …`. Rewrite using `[e1, Finset.sum_add_distrib, e3, Finset.sum_comm, e2, Finset.sum_const, card_highS hkm, ← Nat.cast_smul_eq_nsmul ℂ (m - k), Nat.cast_sub hkm]`. Establish `hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), (Om E₁ j w + Om E₂ j w + ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w + (n:ℂ) • w) = ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), c • w` using `Finset.sum_congr rfl fun j _ => contr E₁ E₂ c w hw j`.

Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, card_lowS hkm] at hsum`. Rewrite `hsum` using `[hmid]`. Establish `h1` using `hw1`. Rewrite `h1` using `[hT E₁]`. Establish `hT2 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₂ j) w = ((k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁)) • w`.

Rewrite using `[hT E₂]`. Take the linear combination `(norm := module) hsum - h1`. Take `⟨r₂, hr₂⟩` from `eigen_val _ (fun r : ℕ => (k:ℂ) * s₂ + r) L₂ hL₂ w hw0 _ hT2`. Establish `hr : (k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁) = k * s₂ + r₂` using `hr₂`. Establish `hfin : (m:ℂ) * k = m * n + n * (r₁ + r₂)`.

Take the linear combination `(n:ℂ) * hr + (k:ℂ) * eqA`. Establish `hnat : m * k = m * n + n * (r₁ + r₂)` using `by exact_mod_cast hfin`. Establish `h3 : m * (k + 1) ≤ m * n` using `Nat.mul_le_mul_left m hkn`. Use polynomial arithmetic with `[Nat.zero_le (n * (r₁ + r₂))]`. Establish `hall : ∀ k, k ≤ n → k ≤ m ∧ ∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Conclude with `⟨Nat.zero_le _, ξ0, hξ0X, by rwa [alt_zero]⟩`.

Consider the case `succ k ih`. Introduce `hk`. Take `⟨hkm, hP⟩` from `ih (Nat.le_of_succ_le hk)`. Conclude with `key k (Nat.lt_of_succ_le hk) hkm hP`. Conclude with `hall n le_rfl`.
-/
theorem wallAlg_of (hA : TensorGl) (_hJ : JMComm) (hQ : QdetFacts) (hS : Spectrum) : WallAlg := by
  unfold WallAlg
  intro n M _ _ E₁ E₂ h₁ h₂ hcomm s₁ s₂ c hc₁ hc₂ m X hX hperm hOm htot
  obtain ⟨ξ0, hξ0X, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  have eqA : (n:ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c := by
    have tr₁ := (hQ n M E₁ h₁).2.2.1 _ hc₁
    have tr₂ := (hQ n M E₂ h₂).2.2.1 _ hc₂
    have key1 := trace_rel E₁ E₂ c _ _ ξ0 tr₁ tr₂ (fun a b => htot a b ξ0 hξ0X)
    have e := smul_left_injective ℂ hξ0 key1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    linear_combination e
  refine ⟨eqA, fun hm => ?_⟩
  have hOmC : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m), pm σ * Om E₁ p = Om E₁ (σ p) * pm σ :=
    (hA n M (Fin m) E₁ h₁ Finset.univ).2.2.2
  have key : ∀ k, k < n → k ≤ m → (∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0) →
      k < m ∧ ∃ ξ ∈ X, alt (firstG m (k + 1)) ξ ≠ 0 := by
    intro k hkn hkm hPk
    by_contra hneg
    have hout : ∀ ξ ∈ X, ∀ i : Fin m, k ≤ (i:ℕ) →
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) = alt (firstG m k) ξ := by
      intro ξ hξ i hi
      have hk : k < m := lt_of_le_of_lt hi i.isLt
      have hz : ∀ η ∈ X, alt (firstG m (k + 1)) η = 0 := by
        intro η hη
        by_contra hne
        exact hneg ⟨hk, η, hη, hne⟩
      exact outer hk X hperm hz ξ hξ i hi
    have hsw : ∀ ξ : TV n M (Fin m), ∀ i j : Fin m, i ≠ j → (i:ℕ) < k → (j:ℕ) < k →
        pm (Equiv.swap i j) (alt (firstG m k) ξ) = -alt (firstG m k) ξ := by
      intro ξ i j hij hi hj
      have hmem : Equiv.swap i j ∈ firstG m k := by
        rw [mem_firstG]
        intro l hl
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          rw [h] at hl
          omega
        · intro h
          rw [h] at hl
          omega
      rw [pm_alt_first _ hmem, Equiv.Perm.sign_swap hij]
      simp
    have hinv : ∀ y ∈ X.map (alt (firstG m k)),
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₁ j) y ∈ X.map (alt (firstG m k)) := by
      intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := Submodule.mem_map.mp hy
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j hj => Submodule.sum_mem _ fun i hi => ?_)
      · rw [← om_alt E₁ hOmC k ξ]
        exact Submodule.mem_map_of_mem (Submodule.sum_mem _ fun j _ => hOm j ξ hξ)
      · have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        rw [hsw ξ i j (ne_of_lt hi') (lt_trans (show (i:ℕ) < (j:ℕ) from hi') hj') hj']
        exact Submodule.neg_mem _ (Submodule.mem_map_of_mem hξ)
    obtain ⟨ξ1, hξ1X, hξ1⟩ := hPk
    obtain ⟨L₁, hL₁⟩ := (hS n M E₁ h₁ (fun _ => s₁) s₁ hc₁ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨L₂, hL₂⟩ := (hS n M E₂ h₂ (fun _ => s₂) s₂ hc₂ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨w, hwY, hw0, r₁, hw1⟩ := eigen (X.map (alt (firstG m k))) _ hinv
      (fun r : ℕ => (k:ℂ) * s₁ + r) L₁ hL₁ (alt (firstG m k) ξ1) (Submodule.mem_map_of_mem hξ1X) hξ1
    obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hwY
    have hwX : alt (firstG m k) ζ ∈ X := alt_mem X hperm ζ hζ
    have hw := fun a b => htot a b _ hwX
    set w := alt (firstG m k) ζ with hwdef
    have hT : ∀ E : Fin n → Fin n → Module.End ℂ M, (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E j) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), Om E j w +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w := by
      intro E
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    have hsplit : ∀ j : Fin m, (j:ℕ) < k →
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
          ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w := by
      intro j hj
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h1 : p = j
      · subst h1
        simp [not_le.mpr hj]
      · by_cases h2 : (p:ℕ) < k
        · simp [h1, h2, not_le.mpr h2]
        · simp [h1, h2, not_lt.mp h2]
    have e1 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), (∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w) :=
      Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_filter.mp hj).2
    have e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j p) w =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), w :=
      Finset.sum_congr rfl fun p hp => hout ζ hζ p (Finset.mem_filter.mp hp).2
    have e3 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w :=
      symm_sum (fun i j => pm (Equiv.swap i j) w) (fun i j => by simp only [Equiv.swap_comm i j])
    have hmid : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w +
          ((m:ℂ) - k) • w := by
      rw [e1, Finset.sum_add_distrib, e3, Finset.sum_comm, e2, Finset.sum_const, card_highS hkm,
        ← Nat.cast_smul_eq_nsmul ℂ (m - k), Nat.cast_sub hkm]
    have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k),
        (Om E₁ j w + Om E₂ j w + ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w + (n:ℂ) • w) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), c • w :=
      Finset.sum_congr rfl fun j _ => contr E₁ E₂ c w hw j
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_lowS hkm] at hsum
    rw [hmid] at hsum
    have h1 := hw1
    rw [hT E₁] at h1
    have hT2 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₂ j) w =
        ((k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁)) • w := by
      rw [hT E₂]
      linear_combination (norm := module) hsum - h1
    obtain ⟨r₂, hr₂⟩ := eigen_val _ (fun r : ℕ => (k:ℂ) * s₂ + r) L₂ hL₂ w hw0 _ hT2
    have hr : (k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁) = k * s₂ + r₂ := hr₂
    have hfin : (m:ℂ) * k = m * n + n * (r₁ + r₂) := by
      linear_combination (n:ℂ) * hr + (k:ℂ) * eqA
    have hnat : m * k = m * n + n * (r₁ + r₂) := by exact_mod_cast hfin
    have h3 : m * (k + 1) ≤ m * n := Nat.mul_le_mul_left m hkn
    nlinarith [Nat.zero_le (n * (r₁ + r₂))]
  have hall : ∀ k, k ≤ n → k ≤ m ∧ ∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Nat.zero_le _, ξ0, hξ0X, by rwa [alt_zero]⟩
    | succ k ih =>
      intro hk
      obtain ⟨hkm, hP⟩ := ih (Nat.le_of_succ_le hk)
      exact key k (Nat.lt_of_succ_le hk) hkm hP
  exact hall n le_rfl

end PositivityTheory.Rg.Cz

end
