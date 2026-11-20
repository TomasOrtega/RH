import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap

open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `k b L N hN hL hvan x hx`. Use `set K : Submodule ℝ (A0 k) := (ℝ ∙ b)ᗮ with hK`. Establish `memK : ∀ y : A0 k, y ∈ K ↔ ⟪y, b⟫_ℝ = 0` using `fun y => by`. Rewrite using `[hK, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]`. Establish `hopen : ∀ b' ∈ (L : Set (A0 k)), IsOpen {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0}` using `fun b' _ => isOpen_ne_fun (by fun_prop) continuous_const`.

Establish `hdense : ∀ b' ∈ (L : Set (A0 k)), Dense {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0}`. Introduce `b' hb'`. Set `P : Submodule ℝ K` to `LinearMap.ker ((innerₛₗ ℝ b').comp K.subtype)`. Establish `hset : {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0} = (P : Set K)ᶜ`. Use extensionality with `y`.

Simplify using `[P, real_inner_comm]`. Rewrite using `[hset, ← interior_eq_empty_iff_dense_compl]`. Assume the negation of the conclusion as `hne`. Establish `htop` using `Submodule.eq_top_of_nonempty_interior' P (Set.nonempty_iff_ne_empty.2 hne)`. Establish `hb'K : b' ∈ Kᗮ`.

Rewrite using `[Submodule.mem_orthogonal]`. Introduce `y hy`. Establish `: (⟨y, hy⟩ : K) ∈ P` using `htop ▸ Submodule.mem_top`. Establish `h' : ⟪b', y⟫_ℝ = 0` using `by simpa [P] using this`. Rewrite `h'` using `[real_inner_comm]`. Then use the resulting hypothesis.

Rewrite `hb'K` using `[hK, Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton]`. Take `⟨r, hr⟩` from `hb'K`. Conclude with `hL b' hb' r hr.symm`. Establish `hD : Dense (⋂ b' ∈ (L : Set (A0 k)), {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0})` using `dense_biInter_of_isOpen hopen L.countable_toSet hdense`. Establish `heq` using `Continuous.ext_on hD (hN.comp continuous_subtype_val) continuous_const (by`.

Introduce `y hy`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq] at hy`. Conclude with `hvan y ((memK y).1 y.2) hy)`. Conclude with `congrFun heq ⟨x, (memK x).2 hx⟩`.
-/
theorem vanish_on_hyperplane_of_vanish_off_others :
    ∀ {k : ℕ} (b : A0 k) (L : Finset (A0 k)) (N : A0 k → ℂ), Continuous N → (∀ b' ∈ L, ∀ r : ℝ, b' ≠ r • b) →
  (∀ x, ⟪x, b⟫_ℝ = 0 → (∀ b' ∈ L, ⟪x, b'⟫_ℝ ≠ 0) → N x = 0) → ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0 := by
  intro k b L N hN hL hvan x hx
  set K : Submodule ℝ (A0 k) := (ℝ ∙ b)ᗮ with hK
  have memK : ∀ y : A0 k, y ∈ K ↔ ⟪y, b⟫_ℝ = 0 := fun y => by
    rw [hK, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
  have hopen : ∀ b' ∈ (L : Set (A0 k)), IsOpen {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0} := fun b' _ =>
    isOpen_ne_fun (by fun_prop) continuous_const
  have hdense : ∀ b' ∈ (L : Set (A0 k)), Dense {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0} := by
    intro b' hb'
    let P : Submodule ℝ K := LinearMap.ker ((innerₛₗ ℝ b').comp K.subtype)
    have hset : {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0} = (P : Set K)ᶜ := by
      ext y; simp [P, real_inner_comm]
    rw [hset, ← interior_eq_empty_iff_dense_compl]
    by_contra hne
    have htop := Submodule.eq_top_of_nonempty_interior' P (Set.nonempty_iff_ne_empty.2 hne)
    have hb'K : b' ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have : (⟨y, hy⟩ : K) ∈ P := htop ▸ Submodule.mem_top
      have h' : ⟪b', y⟫_ℝ = 0 := by simpa [P] using this
      rwa [real_inner_comm] at h'
    rw [hK, Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton] at hb'K
    obtain ⟨r, hr⟩ := hb'K
    exact hL b' hb' r hr.symm
  have hD : Dense (⋂ b' ∈ (L : Set (A0 k)), {y : K | ⟪(y : A0 k), b'⟫_ℝ ≠ 0}) :=
    dense_biInter_of_isOpen hopen L.countable_toSet hdense
  have heq := Continuous.ext_on hD (hN.comp continuous_subtype_val) continuous_const (by
    intro y hy
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
    exact hvan y ((memK y).1 y.2) hy)
  exact congrFun heq ⟨x, (memK x).2 hx⟩

end GlobalTheory
