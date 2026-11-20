import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLeMaximalIdealPowSmulOfDirected

open IsLocalRing

namespace GlobalTheory.Chevalley

/- English proof (translation)
Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal A) A n F)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing, LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]`. Use `first`. Consider the case `rw [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply, ← ha, sub_self]`.

Consider the case `simp [← ha]`.
-/
theorem exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (F : AdicCompletion (maximalIdeal A) A) (n : ℕ) :
    ∃ a : A, F - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal A) A n F)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing,
    LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  first
  | rw [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply, ← ha, sub_self]
  | simp [← ha]

/- English proof (translation)
Introduce `A _ _ _ K J hK hmK hJ k`. Set `B` to `AdicCompletion (maximalIdeal A) A`. Use `haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _`. Use `haveI : Module.Flat A B := AdicCompletion.flat_of_isNoetherian _`. Use `haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom`.

Set `f` to `algebraMap A B`. Establish `hmB : ∀ n, maximalIdeal B ^ n = (maximalIdeal A ^ n).map f` using `fun n ↦ by`. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]`. Set `K' : ℕ → Ideal B` to `fun e ↦ (K e).map f`. Establish `hK' : Antitone K'` using `fun i j hij ↦ Ideal.map_mono (hK hij)`.

Establish `hmK' : ∀ e, maximalIdeal B ^ e ≤ K' e` using `fun e ↦ by`. Rewrite using `[hmB]`. Conclude with `Ideal.map_mono (hmK e)`. Set `N : Ideal B` to `⨅ e, K' e`. Establish `hNK : ∀ e, N ≤ K' e` using `fun e ↦ iInf_le _ e`.

Establish `hNJ : N ≤ J.map f`. Introduce `F hF`. Use `choose a ha using exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion A F`. Use `hJ F a ha fun n ↦ ?_` and prove the remaining obligations. Establish `h1 : f (a n) ∈ K' n`.

Establish `: f (a n) = F - (F - f (a n))` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (hNK n hF) (hmK' n (ha n))`. Rewrite using `[← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (K n)]`. Conclude with `h1`.

Set `P : ℕ → Submodule B (B ⧸ N)` to `fun e ↦ Submodule.map (Submodule.mkQ N) (K' e : Submodule B B)`. Establish `hdir : Directed (· ≥ ·) P` using `fun i j ↦ ⟨max i j, Submodule.map_mono (hK' (le_max_left i j)), Submodule.map_mono (hK' (le_max_right i j))⟩`. Establish `hbot : (⨅ e, P e) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective N x`. Rewrite using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite `hx`, the goal using `[Submodule.mem_iInf]`. Introduce `e`. Use `Submodule.mem_comap.2 (hx e)` as an intermediate fact.

Rewrite `this` using `[Submodule.comap_map_mkQ, sup_eq_right.2 (hNK e)]`. Conclude with `this`. Take `⟨e, he⟩` from `exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ N) ℕ P ⟨0⟩ hdir hbot k`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `hsm : (maximalIdeal B ^ k • (⊤ : Submodule B (B ⧸ N))) = Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B)`.

Establish `hI : (maximalIdeal B ^ k • (⊤ : Submodule B B)) = (maximalIdeal B ^ k : Submodule B B)`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Rewrite using `[← Submodule.range_mkQ N, LinearMap.range_eq_map, ← Submodule.map_smul'', hI]`. Establish `h2 : K' e ≤ maximalIdeal B ^ k ⊔ N`. Introduce `y hy`.

Establish `h` using `he (Submodule.mem_map_of_mem (f := Submodule.mkQ N) hy)`. Rewrite `h` using `[hsm]`. Establish `h' : y ∈ Submodule.comap (Submodule.mkQ N) (Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B))` using `h`. Rewrite `h'` using `[Submodule.comap_map_mkQ]`. Rewrite using `[sup_comm]`.

Conclude with `h'`. Establish `h3 : K' e ≤ (J ⊔ maximalIdeal A ^ k).map f`. Rewrite using `[Ideal.map_sup, ← hmB]`. Conclude with `h2.trans (sup_le le_sup_right (hNJ.trans le_sup_left))`. Rewrite using `[← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J ⊔ maximalIdeal A ^ k)]`.

Conclude with `Ideal.map_le_iff_le_comap.1 h3`.
-/
theorem exists_le_sup_maximalIdeal_pow_of_antitone :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A),
      Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) →
      (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A),
        (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) →
        (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) →
      ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  intro A _ _ _ K J hK hmK hJ k
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : Module.Flat A B := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let f := algebraMap A B
  have hmB : ∀ n, maximalIdeal B ^ n = (maximalIdeal A ^ n).map f := fun n ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]
  let K' : ℕ → Ideal B := fun e ↦ (K e).map f
  have hK' : Antitone K' := fun i j hij ↦ Ideal.map_mono (hK hij)
  have hmK' : ∀ e, maximalIdeal B ^ e ≤ K' e := fun e ↦ by
    rw [hmB]; exact Ideal.map_mono (hmK e)
  let N : Ideal B := ⨅ e, K' e
  have hNK : ∀ e, N ≤ K' e := fun e ↦ iInf_le _ e
  have hNJ : N ≤ J.map f := by
    intro F hF
    choose a ha using exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion A F
    refine hJ F a ha fun n ↦ ?_
    have h1 : f (a n) ∈ K' n := by
      have : f (a n) = F - (F - f (a n)) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hNK n hF) (hmK' n (ha n))
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (K n)]
    exact h1
  let P : ℕ → Submodule B (B ⧸ N) := fun e ↦ Submodule.map (Submodule.mkQ N) (K' e : Submodule B B)
  have hdir : Directed (· ≥ ·) P := fun i j ↦
    ⟨max i j, Submodule.map_mono (hK' (le_max_left i j)), Submodule.map_mono (hK' (le_max_right i j))⟩
  have hbot : (⨅ e, P e) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mem_iInf] at hx ⊢
    intro e
    have := Submodule.mem_comap.2 (hx e)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (hNK e)] at this
    exact this
  obtain ⟨e, he⟩ := exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ N) ℕ P ⟨0⟩ hdir hbot k
  refine ⟨e, ?_⟩
  have hsm : (maximalIdeal B ^ k • (⊤ : Submodule B (B ⧸ N))) =
      Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B) := by
    have hI : (maximalIdeal B ^ k • (⊤ : Submodule B B)) = (maximalIdeal B ^ k : Submodule B B) := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ N, LinearMap.range_eq_map, ← Submodule.map_smul'', hI]
  have h2 : K' e ≤ maximalIdeal B ^ k ⊔ N := by
    intro y hy
    have h := he (Submodule.mem_map_of_mem (f := Submodule.mkQ N) hy)
    rw [hsm] at h
    have h' : y ∈ Submodule.comap (Submodule.mkQ N)
        (Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B)) := h
    rw [Submodule.comap_map_mkQ] at h'
    rw [sup_comm]; exact h'
  have h3 : K' e ≤ (J ⊔ maximalIdeal A ^ k).map f := by
    rw [Ideal.map_sup, ← hmB]
    exact h2.trans (sup_le le_sup_right (hNJ.trans le_sup_left))
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J ⊔ maximalIdeal A ^ k)]
  exact Ideal.map_le_iff_le_comap.1 h3

end GlobalTheory.Chevalley
