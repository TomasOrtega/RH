import Mathlib

namespace GlobalTheory.SmulMemOfMemSpan

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `M.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm a b, mul_smul]`.

Conclude with `M.smul_mem b hax`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem a hby`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors R) c`. Simplify using `only at hnd`. Use `⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩` and prove the remaining obligations. Establish `key : (d : R) • c • x = n • x`. Rewrite using `[← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]`.

Rewrite using `[mul_comm (d : R) a, mul_smul, key, smul_comm a n x]`. Conclude with `M.smul_mem n hax`.
-/
theorem exists_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ _ M v hv`. Conclude with `exists_smul_mem_of_mem_span M hv`.
-/
theorem main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv

end GlobalTheory.SmulMemOfMemSpan
