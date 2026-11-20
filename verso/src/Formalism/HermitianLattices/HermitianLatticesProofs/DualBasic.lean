import Mathlib
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Simplify using `only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`.
-/
theorem dualBasic_mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ h hs hst`. Establish `anti : ∀ L M : Submodule R V, L ≤ M → dual h M ≤ dual h L`. Introduce `L M hLM x hx`. Rewrite `hx`, the goal using `[dualBasic_mem_dual]`. Conclude with `fun y hy => hx y (hLM hy)`.

Establish `starOne : ∀ z : K, z ∈ (1 : Submodule R K) → star z ∈ (1 : Submodule R K)`. Introduce `z hz`. Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hz`. Take `⟨t, ht⟩` from `hst r`. Conclude with `Submodule.mem_one.2 ⟨t, ht⟩`.

Establish `integ : ∀ L : Submodule R V, IsIntegralLat h L ↔ L ≤ dual h L`. Introduce `L`. Prove the components needed by the constructor for the conclusion. Introduce `hL x hx`. Rewrite using `[dualBasic_mem_dual]`.

Conclude with `fun y hy => hL y hy x hx`. Introduce `hL x hx y hy`. Conclude with `(dualBasic_mem_dual h L y).1 (hL hy) x hx`. Use `⟨anti, ?_, ?_, integ, ?_⟩` and prove the remaining obligations. Introduce `L x hx`.

Rewrite using `[dualBasic_mem_dual]`. Introduce `y hy`. Establish `h1 : h x y ∈ (1 : Submodule R K)` using `(dualBasic_mem_dual h L y).1 hy x hx`. Establish `h2` using `starOne _ h1`. Establish `h3` using `hs.eq x y`.

Simplify using `only [starRingEnd_apply] at h3`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Introduce `L M`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_inf (anti _ _ le_sup_left) (anti _ _ le_sup_right)`.

Introduce `x hx`. Take `⟨hxL, hxM⟩` from `Submodule.mem_inf.1 hx`. Rewrite `hxL`, `hxM`, the goal using `[dualBasic_mem_dual]`. Introduce `y hy`. Take `⟨l, hl, m, hm, rfl⟩` from `Submodule.mem_sup.1 hy`.

Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `add_mem (hxL l hl) (hxM m hm)`. Introduce `L`. Rewrite using `[IsUnimodular, integ, le_antisymm_iff]`. Conclude with `⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩`.
-/
theorem dualBasic : DualBasic := by
  intro R K V _ _ _ _ _ _ _ _ h hs hst
  have anti : ∀ L M : Submodule R V, L ≤ M → dual h M ≤ dual h L := by
    intro L M hLM x hx
    rw [dualBasic_mem_dual] at hx ⊢
    exact fun y hy => hx y (hLM hy)
  have starOne : ∀ z : K, z ∈ (1 : Submodule R K) → star z ∈ (1 : Submodule R K) := by
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hz
    obtain ⟨t, ht⟩ := hst r
    exact Submodule.mem_one.2 ⟨t, ht⟩
  have integ : ∀ L : Submodule R V, IsIntegralLat h L ↔ L ≤ dual h L := by
    intro L
    constructor
    · intro hL x hx
      rw [dualBasic_mem_dual]
      exact fun y hy => hL y hy x hx
    · intro hL x hx y hy
      exact (dualBasic_mem_dual h L y).1 (hL hy) x hx
  refine ⟨anti, ?_, ?_, integ, ?_⟩
  · intro L x hx
    rw [dualBasic_mem_dual]
    intro y hy
    have h1 : h x y ∈ (1 : Submodule R K) := (dualBasic_mem_dual h L y).1 hy x hx
    have h2 := starOne _ h1
    have h3 := hs.eq x y
    simp only [starRingEnd_apply] at h3
    rwa [h3] at h2
  · intro L M
    apply le_antisymm
    · exact le_inf (anti _ _ le_sup_left) (anti _ _ le_sup_right)
    · intro x hx
      obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
      rw [dualBasic_mem_dual] at hxL hxM ⊢
      intro y hy
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply]
      exact add_mem (hxL l hl) (hxM m hm)
  · intro L
    rw [IsUnimodular, integ, le_antisymm_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

end Formalism.HermitianLatticesTheory
