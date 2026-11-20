import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

/- English proof (translation)
Introduce `M T R _ _ _ _ j Op Rel K N hspan hOp hRel hRad hsup`. Establish `h1 : ∀ e ∈ Algebra.adjoin ℂ Op, ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (e x)) ∧ ∀ t ∈ N, Φ t ∈ N`. Introduce `e he`. Proceed by induction on `he using Algebra.adjoin_induction with`. Consider the case `mem g hg => exact hOp g hg`.

Consider the case `algebraMap c`. Use `⟨c • (1 : Module.End ℂ T), fun r x => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Simplify using `using N.smul_mem c ht`. Consider the case `add a b _ _ ha hb`.

Take `⟨A, hA, hAN⟩` from `ha`. Take `⟨B, hB, hBN⟩` from `hb`. Use `⟨A + B, fun r x => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Simplify using `[hA, hB]`. Simplify using `using N.add_mem (hAN t ht) (hBN t ht)`.

Consider the case `mul a b _ _ ha hb`. Take `⟨A, hA, hAN⟩` from `ha`. Take `⟨B, hB, hBN⟩` from `hb`. Use `⟨A * B, fun r x => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Simplify using `[hA, hB]`.

Simplify using `using hAN _ (hBN t ht)`. Establish `h2 : ∀ u ∈ (⨆ r, K.map (j r)), ∃ S : Finset M, (∀ k ∈ S, k ∈ K) ∧ ∀ (e : Module.End ℂ M) (Φ : Module.End ℂ T), (∀ r x, Φ (j r x) = j r (e x)) → (∀ k ∈ S, e k ∈ Rel) → Φ u ∈ N`. Introduce `u hu`. Proceed by induction on `hu using Submodule.iSup_induction' with`. Consider the case `mem r x hx`.

Take `⟨k, hk, rfl⟩` from `hx`. Use `⟨{k}, by simpa using hk, fun e Φ hΦ hS => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Conclude with `hRel r _ (hS k (Finset.mem_singleton_self k))`. Consider the case `zero => exact ⟨∅, by simp, fun e Φ _ _ => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨S, hS, hS'⟩` from `hx`. Take `⟨S2, hS2, hS2'⟩` from `hy`. Use `⟨S ∪ S2, fun k hk => ?_, fun e Φ hΦ h => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 hk with h | h` into its components or cases.

Conclude with `hS k h`. Conclude with `hS2 k h`. Rewrite using `[map_add]`. Conclude with `N.add_mem (hS' e Φ hΦ fun k hk => h k (Finset.mem_union_left _ hk)) (hS2' e Φ hΦ fun k hk => h k (Finset.mem_union_right _ hk))`. Take `⟨s, hGen, hs⟩` from `hRad`.

Establish `h3 : ∀ r, j r s ∈ N`. Introduce `r`. Establish `hm : j r s ∈ N ⊔ (⨆ r, K.map (j r))` using `by rw [hsup]; trivial`. Take `⟨n, hn, u, hu, hnu⟩` from `Submodule.mem_sup.1 hm`. Take `⟨S, hSK, hS⟩` from `h2 u hu`.

Take `⟨e, he, hes, heS⟩` from `hs S hSK`. Take `⟨Φ, hΦ, hΦN⟩` from `h1 e he`. Establish `: j r s = Φ n + Φ u` using `by rw [← map_add, hnu, hΦ, hes]`. Rewrite using `[this]`. Conclude with `N.add_mem (hΦN n hn) (hS e Φ hΦ heS)`.

Establish `h4 : ∀ r, N.comap (j r) = ⊤`. Introduce `r`. Use `hGen _ (fun x hx => hRel r x hx) (fun g hg x hx => ?_) (h3 r)` and prove the remaining obligations. Take `⟨Φ, hΦ, hΦN⟩` from `hOp g hg`. Use `show j r (g x) ∈ N`.

Rewrite using `[← hΦ]`. Conclude with `hΦN _ hx`. Rewrite using `[eq_top_iff, ← hspan]`. Use `iSup_le fun r => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `: x ∈ N.comap (j r)` using `by rw [h4 r]; trivial`. Conclude with `this`.
-/
theorem UpperTheory.Lit.HoweDuality.nak :
    ∀ {M T R : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T] (j : R → M →ₗ[ℂ] T) (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (N : Submodule ℂ T), (⨆ r, LinearMap.range (j r)) = ⊤ → (∀ g ∈ Op, ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (g x)) ∧ ∀ t ∈ N, Φ t ∈ N) → (∀ r, ∀ x ∈ Rel, j r x ∈ N) → RadFin Op Rel K → N ⊔ (⨆ r, K.map (j r)) = ⊤ → N = ⊤ := by
  intro M T R _ _ _ _ j Op Rel K N hspan hOp hRel hRad hsup
  classical
  have h1 : ∀ e ∈ Algebra.adjoin ℂ Op,
      ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (e x)) ∧ ∀ t ∈ N, Φ t ∈ N := by
    intro e he
    induction he using Algebra.adjoin_induction with
    | mem g hg => exact hOp g hg
    | algebraMap c =>
      refine ⟨c • (1 : Module.End ℂ T), fun r x => ?_, fun t ht => ?_⟩
      · simp [Algebra.algebraMap_eq_smul_one]
      · simpa using N.smul_mem c ht
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A + B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using N.add_mem (hAN t ht) (hBN t ht)
    | mul a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A * B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using hAN _ (hBN t ht)
  have h2 : ∀ u ∈ (⨆ r, K.map (j r)), ∃ S : Finset M, (∀ k ∈ S, k ∈ K) ∧
      ∀ (e : Module.End ℂ M) (Φ : Module.End ℂ T), (∀ r x, Φ (j r x) = j r (e x)) →
        (∀ k ∈ S, e k ∈ Rel) → Φ u ∈ N := by
    intro u hu
    induction hu using Submodule.iSup_induction' with
    | mem r x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨{k}, by simpa using hk, fun e Φ hΦ hS => ?_⟩
      rw [hΦ]
      exact hRel r _ (hS k (Finset.mem_singleton_self k))
    | zero => exact ⟨∅, by simp, fun e Φ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨S, hS, hS'⟩ := hx
      obtain ⟨S2, hS2, hS2'⟩ := hy
      refine ⟨S ∪ S2, fun k hk => ?_, fun e Φ hΦ h => ?_⟩
      · rcases Finset.mem_union.1 hk with h | h
        · exact hS k h
        · exact hS2 k h
      · rw [map_add]
        exact N.add_mem (hS' e Φ hΦ fun k hk => h k (Finset.mem_union_left _ hk))
          (hS2' e Φ hΦ fun k hk => h k (Finset.mem_union_right _ hk))
  obtain ⟨s, hGen, hs⟩ := hRad
  have h3 : ∀ r, j r s ∈ N := by
    intro r
    have hm : j r s ∈ N ⊔ (⨆ r, K.map (j r)) := by rw [hsup]; trivial
    obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.1 hm
    obtain ⟨S, hSK, hS⟩ := h2 u hu
    obtain ⟨e, he, hes, heS⟩ := hs S hSK
    obtain ⟨Φ, hΦ, hΦN⟩ := h1 e he
    have : j r s = Φ n + Φ u := by rw [← map_add, hnu, hΦ, hes]
    rw [this]
    exact N.add_mem (hΦN n hn) (hS e Φ hΦ heS)
  have h4 : ∀ r, N.comap (j r) = ⊤ := by
    intro r
    refine hGen _ (fun x hx => hRel r x hx) (fun g hg x hx => ?_) (h3 r)
    obtain ⟨Φ, hΦ, hΦN⟩ := hOp g hg
    show j r (g x) ∈ N
    rw [← hΦ]
    exact hΦN _ hx
  rw [eq_top_iff, ← hspan]
  refine iSup_le fun r => ?_
  rintro _ ⟨x, rfl⟩
  have : x ∈ N.comap (j r) := by rw [h4 r]; trivial
  exact this
