import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimKer

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `R σ _ _ F hF I M _ _ y a k hI hak hq`. Use `set Y : Ideal R := Ideal.span (Set.range y) with hY`. Establish `hYfg : Y.FG` using `⟨(Set.finite_range y).toFinset, by simp [hY]⟩`. Establish `hK : Antitone (fun j ↦ Y ^ k ⊔ I j)` using `fun i j hij ↦ sup_le_sup_left (hI hij) _`. Establish `hk1 : Y ^ k ≤ Y ^ (a + 1)` using `Ideal.pow_le_pow_right (by omega)`.

Introduce `c hc`. Use `choose p hp using fun α ↦ ULim.mk_surjective F (fun j ↦ Y ^ k ⊔ I j) M (c α)`. Establish `hsum : ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • c α = ULim.mk F (fun j ↦ Y ^ k ⊔ I j) M (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N)`. Establish `e : (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) = ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α`. Use extensionality with `N`.

Simplify using `[Finset.sum_apply]`. Rewrite using `[e, map_sum]`. Simplify using `[hp]`. Rewrite `hc` using `[sup_bot_eq, hsum, ULim.mem_smul_top_iff R F hF _ M (Y ^ (a + 1)) hYfg.pow hK]`. Introduce `α`.

Rewrite using `[sup_bot_eq, ← hp α, ULim.mem_smul_top_iff R F hF _ M Y hYfg hK]`. Introduce `j`. Use `filter_upwards [hc j, hq j] with N hN hqN`. Establish `hN' : ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑β • p β N ∈ (Y ^ (a + 1) ⊔ I j) • (⊤ : Submodule R (M N))` using `Submodule.smul_mono_left (sup_le le_sup_left (sup_le (hk1.trans le_sup_left) le_sup_right)) hN`. Conclude with `Submodule.smul_mono_left (sup_le_sup_left le_sup_right Y) (hqN (fun β ↦ p β N) hN' α)`.
-/
theorem UpperTheory.V.AlgebraTools.qRegAt_uLim :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (y : σ → R) (a k : ℕ), Antitone I → a < k →
      (∀ j, ∀ᶠ N in F, QRegAt (M N) y (I j) a) →
      QRegAt (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ I j) M) y ⊥ a := by
  intro R σ _ _ F hF I M _ _ y a k hI hak hq
  classical
  set Y : Ideal R := Ideal.span (Set.range y) with hY
  have hYfg : Y.FG := ⟨(Set.finite_range y).toFinset, by simp [hY]⟩
  have hK : Antitone (fun j ↦ Y ^ k ⊔ I j) := fun i j hij ↦ sup_le_sup_left (hI hij) _
  have hk1 : Y ^ k ≤ Y ^ (a + 1) := Ideal.pow_le_pow_right (by omega)
  intro c hc
  choose p hp using fun α ↦ ULim.mk_surjective F (fun j ↦ Y ^ k ⊔ I j) M (c α)
  have hsum : ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • c α =
      ULim.mk F (fun j ↦ Y ^ k ⊔ I j) M
        (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) := by
    have e : (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) =
        ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α := by
      ext N
      simp [Finset.sum_apply]
    rw [e, map_sum]
    simp [hp]
  rw [sup_bot_eq, hsum, ULim.mem_smul_top_iff R F hF _ M (Y ^ (a + 1)) hYfg.pow hK] at hc
  intro α
  rw [sup_bot_eq, ← hp α, ULim.mem_smul_top_iff R F hF _ M Y hYfg hK]
  intro j
  filter_upwards [hc j, hq j] with N hN hqN
  have hN' : ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑β • p β N ∈
      (Y ^ (a + 1) ⊔ I j) • (⊤ : Submodule R (M N)) :=
    Submodule.smul_mono_left (sup_le le_sup_left (sup_le (hk1.trans le_sup_left) le_sup_right)) hN
  exact Submodule.smul_mono_left (sup_le_sup_left le_sup_right Y) (hqN (fun β ↦ p β N) hN' α)
