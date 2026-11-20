import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock

namespace GlobalTheory.ChainSplit

variable {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [CommMonoid G]

/- English proof (translation)
Use `show ρ g * ρ h = ρ h * ρ g`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem rho_commute (ρ : G →* Module.End ℂ V) (g h : G) : Commute (ρ g) (ρ h) := by
  show ρ g * ρ h = ρ h * ρ g
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Introduce `i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Introduce `v hv g`. Rewrite `hv` using `[h0, Submodule.mem_bot]`.

Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ t`. Introduce `v hv g`. Establish `h1` using `hmono (Fin.castSucc_lt_succ (i := t)).le (hstep t v hv g)`.

Establish `h2 : ρ g v = (ρ g v - c t g • v) + c t g • v` using `by abel`. Rewrite using `[h2]`. Conclude with `(S t.succ).add_mem h1 ((S t.succ).smul_mem _ hv)`.
-/
theorem stable (ρ : G →* Module.End ℂ V) (M : ℕ) (S : Fin (M + 1) → Submodule ℂ V)
    (c : Fin M → G → ℂ) (hmono : Monotone S) (h0 : S 0 = ⊥)
    (hstep : ∀ t : Fin M, ∀ v ∈ S t.succ, ∀ g, ρ g v - c t g • v ∈ S t.castSucc) :
    ∀ i : Fin (M + 1), ∀ v ∈ S i, ∀ g, ρ g v ∈ S i := by
  intro i
  induction i using Fin.cases with
  | zero =>
    intro v hv g
    rw [h0, Submodule.mem_bot] at hv
    subst hv
    simp
  | succ t =>
    intro v hv g
    have h1 := hmono (Fin.castSucc_lt_succ (i := t)).le (hstep t v hv g)
    have h2 : ρ g v = (ρ g v - c t g • v) + c t g • v := by abel
    rw [h2]
    exact (S t.succ).add_mem h1 ((S t.succ).smul_mem _ hv)

/- English proof (translation)
Introduce `T`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `_`. Use `⟨1, fun g => Commute.one_left _, by simp, 1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `v _`.

Simplify using the standard rewrite rules. Introduce `j T hj ih hk`. Establish `hjk : j ≠ k` using `fun h => hk (h ▸ Finset.mem_insert_self j T)`. Establish `hkT : k ∉ T` using `fun h => hk (Finset.mem_insert_of_mem h)`. Take `⟨P, hPc, hPk, K, hK, hPv⟩` from `ih hkT`.

Take `⟨g, hg⟩` from `hdist j k hjk`. Establish `hfc : ∀ h, Commute (ρ g - c j g • (1 : Module.End ℂ V)) (ρ h)` using `fun h => ((rho_commute ρ g h).sub_left ((Commute.one_left _).smul_left _))`. Establish `hfP : Commute (ρ g - c j g • (1 : Module.End ℂ V)) P` using `((hPc g).symm).sub_left ((Commute.one_left _).smul_left _)`. Use `⟨(ρ g - c j g • (1 : Module.End ℂ V)) * P, fun h => (hfc h).mul_left (hPc h), ?_, (c k g - c j g) * K, mul_ne_zero (sub_ne_zero.mpr (Ne.symm hg)) hK, ?_⟩` and prove the remaining obligations. Introduce `s hs x hx`.

Break down `Finset.mem_insert.mp hs with rfl | hs` into its components or cases. Rewrite using `[hfP.eq, Module.End.mul_apply]`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx, sub_self, map_zero]`. Rewrite using `[Module.End.mul_apply, hPk s hs x hx, map_zero]`. Introduce `v hv`.

Establish `hu` using `hPv v hv`. Establish `key : ((ρ g - c j g • (1 : Module.End ℂ V)) * P) v - ((c k g - c j g) * K) • v = (ρ g (P v - K • v) - c j g • (P v - K • v)) + K • (ρ g v - c k g • v)`. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]`. Use `module`. Rewrite using `[key]`.

Conclude with `(S _).add_mem ((S _).sub_mem (hstab _ _ hu g) ((S _).smul_mem _ hu)) ((S _).smul_mem _ (hstep k v hv g))`.
-/
theorem killer (ρ : G →* Module.End ℂ V) (M : ℕ) (S : Fin (M + 1) → Submodule ℂ V)
    (c : Fin M → G → ℂ)
    (hstab : ∀ i : Fin (M + 1), ∀ v ∈ S i, ∀ g, ρ g v ∈ S i)
    (hstep : ∀ t : Fin M, ∀ v ∈ S t.succ, ∀ g, ρ g v - c t g • v ∈ S t.castSucc)
    (hdist : ∀ s t, s ≠ t → ∃ g, c s g ≠ c t g) (k : Fin M) :
    ∀ T : Finset (Fin M), k ∉ T → ∃ P : Module.End ℂ V, (∀ g, Commute P (ρ g)) ∧
      (∀ s ∈ T, ∀ x : V, (∀ g, ρ g x = c s g • x) → P x = 0) ∧
      ∃ K : ℂ, K ≠ 0 ∧ ∀ v ∈ S k.succ, P v - K • v ∈ S k.castSucc := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro _
    refine ⟨1, fun g => Commute.one_left _, by simp, 1, one_ne_zero, ?_⟩
    intro v _
    simp
  · intro j T hj ih hk
    have hjk : j ≠ k := fun h => hk (h ▸ Finset.mem_insert_self j T)
    have hkT : k ∉ T := fun h => hk (Finset.mem_insert_of_mem h)
    obtain ⟨P, hPc, hPk, K, hK, hPv⟩ := ih hkT
    obtain ⟨g, hg⟩ := hdist j k hjk
    have hfc : ∀ h, Commute (ρ g - c j g • (1 : Module.End ℂ V)) (ρ h) := fun h =>
      ((rho_commute ρ g h).sub_left ((Commute.one_left _).smul_left _))
    have hfP : Commute (ρ g - c j g • (1 : Module.End ℂ V)) P :=
      ((hPc g).symm).sub_left ((Commute.one_left _).smul_left _)
    refine ⟨(ρ g - c j g • (1 : Module.End ℂ V)) * P, fun h => (hfc h).mul_left (hPc h), ?_,
      (c k g - c j g) * K, mul_ne_zero (sub_ne_zero.mpr (Ne.symm hg)) hK, ?_⟩
    · intro s hs x hx
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rw [hfP.eq, Module.End.mul_apply]
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx, sub_self, map_zero]
      · rw [Module.End.mul_apply, hPk s hs x hx, map_zero]
    · intro v hv
      have hu := hPv v hv
      have key : ((ρ g - c j g • (1 : Module.End ℂ V)) * P) v - ((c k g - c j g) * K) • v
          = (ρ g (P v - K • v) - c j g • (P v - K • v)) + K • (ρ g v - c k g • v) := by
        simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, map_sub, map_smul]
        module
      rw [key]
      exact (S _).add_mem ((S _).sub_mem (hstab _ _ hu g) ((S _).smul_mem _ hu))
        ((S _).smul_mem _ (hstep k v hv g))

/- English proof (translation)
Introduce `V _ _ G _ ρ M S c hmono h0 hstep hdist`. Establish `hstab` using `stable ρ M S c hmono h0 hstep`. Establish `main : ∀ i : Fin (M + 1), ∀ v ∈ S i, ∃ w : Fin M → V, v = ∑ t, w t ∧ (∀ t g, ρ g (w t) = c t g • w t) ∧ ∀ t : Fin M, i ≤ t.castSucc → w t = 0`. Introduce `i`. Proceed by induction on `i using Fin.induction with`.

Consider the case `zero`. Introduce `v hv`. Rewrite `hv` using `[h0, Submodule.mem_bot]`. Conclude with `⟨0, by simp [hv], by simp, fun _ _ => rfl⟩`. Consider the case `succ k ih`.

Introduce `v hv`. Take `⟨P, hPc, hPk, K, hK, hPv⟩` from `killer ρ M S c hstab hstep hdist k (Finset.univ.erase k) (Finset.notMem_erase k _)`. Establish `hPS : ∀ x ∈ S k.castSucc, P x = 0`. Introduce `x hx`. Take `⟨w', hsum, heig, hsupp⟩` from `ih x hx`.

Rewrite using `[hsum, map_sum]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s = k`. Substitute `hs` using the available equality. Rewrite using `[hsupp s le_rfl, map_zero]`.

Conclude with `hPk s (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩) _ (heig s)`. Take `⟨w, hw⟩ : ∃ w : V, w = K⁻¹ • P v` from `⟨_, rfl⟩`. Establish `hvw : v - w ∈ S k.castSucc`. Establish `: v - w = (-K⁻¹) • (P v - K • v)`. Rewrite using `[hw, smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hK]`.

Use `module`. Rewrite using `[this]`. Conclude with `(S _).smul_mem _ (hPv v hv)`. Establish `hweig : ∀ g, ρ g w = c k g • w`. Introduce `g`.

Establish `h1 : P (ρ g v - c k g • v) = 0` using `hPS _ (hstep k v hv g)`. Establish `h2 : P (ρ g v) = ρ g (P v)`. Rewrite using `[← Module.End.mul_apply, (hPc g).eq, Module.End.mul_apply]`. Rewrite `h1` using `[map_sub, map_smul, h2, sub_eq_zero]`. Rewrite using `[hw, map_smul, h1, smul_comm]`.

Take `⟨w', hsum, heig, hsupp⟩` from `ih (v - w) hvw`. Use `⟨w' + Pi.single k w, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Rewrite using `[Finset.sum_add_distrib, ← hsum]`. Simplify using the standard rewrite rules.

Introduce `t g`. Distinguish the cases in `ht : t = k`. Substitute `ht` using the available equality. Simplify using `[heig, hweig, smul_add]`. Simplify using `[Pi.single_apply, ht, heig]`.

Introduce `t ht`. Establish `htk : t ≠ k`. Introduce and unpack `rfl`. Conclude with `absurd ht (not_le.mpr (Fin.castSucc_lt_succ (i := t)))`. Establish `: k.castSucc ≤ t.castSucc` using `le_trans (Fin.castSucc_lt_succ (i := k)).le ht`.

Simplify using `[Pi.single_apply, htk, hsupp t this]`. Introduce `v hv`. Take `⟨w, h1, h2, _⟩` from `main _ v hv`. Conclude with `⟨w, h1, h2⟩`.
-/
theorem chain_split : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [CommMonoid G] (ρ : G →* Module.End ℂ V)
    (M : ℕ) (S : Fin (M + 1) → Submodule ℂ V) (c : Fin M → G → ℂ), Monotone S → S 0 = ⊥ →
    (∀ t : Fin M, ∀ v ∈ S t.succ, ∀ g, ρ g v - c t g • v ∈ S t.castSucc) →
    (∀ s t, s ≠ t → ∃ g, c s g ≠ c t g) →
    ∀ v ∈ S (Fin.last M), ∃ w : Fin M → V, v = ∑ t, w t ∧ ∀ t g, ρ g (w t) = c t g • w t := by
  intro V _ _ G _ ρ M S c hmono h0 hstep hdist
  have hstab := stable ρ M S c hmono h0 hstep
  have main : ∀ i : Fin (M + 1), ∀ v ∈ S i, ∃ w : Fin M → V, v = ∑ t, w t ∧
      (∀ t g, ρ g (w t) = c t g • w t) ∧ ∀ t : Fin M, i ≤ t.castSucc → w t = 0 := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro v hv
      rw [h0, Submodule.mem_bot] at hv
      exact ⟨0, by simp [hv], by simp, fun _ _ => rfl⟩
    | succ k ih =>
      intro v hv
      obtain ⟨P, hPc, hPk, K, hK, hPv⟩ := killer ρ M S c hstab hstep hdist k
        (Finset.univ.erase k) (Finset.notMem_erase k _)
      have hPS : ∀ x ∈ S k.castSucc, P x = 0 := by
        intro x hx
        obtain ⟨w', hsum, heig, hsupp⟩ := ih x hx
        rw [hsum, map_sum]
        refine Finset.sum_eq_zero fun s _ => ?_
        by_cases hs : s = k
        · subst hs; rw [hsupp s le_rfl, map_zero]
        · exact hPk s (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩) _ (heig s)
      obtain ⟨w, hw⟩ : ∃ w : V, w = K⁻¹ • P v := ⟨_, rfl⟩
      have hvw : v - w ∈ S k.castSucc := by
        have : v - w = (-K⁻¹) • (P v - K • v) := by
          rw [hw, smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hK]; module
        rw [this]; exact (S _).smul_mem _ (hPv v hv)
      have hweig : ∀ g, ρ g w = c k g • w := by
        intro g
        have h1 : P (ρ g v - c k g • v) = 0 := hPS _ (hstep k v hv g)
        have h2 : P (ρ g v) = ρ g (P v) := by
          rw [← Module.End.mul_apply, (hPc g).eq, Module.End.mul_apply]
        rw [map_sub, map_smul, h2, sub_eq_zero] at h1
        rw [hw, map_smul, h1, smul_comm]
      obtain ⟨w', hsum, heig, hsupp⟩ := ih (v - w) hvw
      refine ⟨w' + Pi.single k w, ?_, ?_, ?_⟩
      · simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib, ← hsum]; simp
      · intro t g
        by_cases ht : t = k
        · subst ht; simp [heig, hweig, smul_add]
        · simp [Pi.single_apply, ht, heig]
      · intro t ht
        have htk : t ≠ k := by
          rintro rfl; exact absurd ht (not_le.mpr (Fin.castSucc_lt_succ (i := t)))
        have : k.castSucc ≤ t.castSucc := le_trans (Fin.castSucc_lt_succ (i := k)).le ht
        simp [Pi.single_apply, htk, hsupp t this]
  intro v hv
  obtain ⟨w, h1, h2, _⟩ := main _ v hv
  exact ⟨w, h1, h2⟩

end GlobalTheory.ChainSplit
