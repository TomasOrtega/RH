import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `n hn`. Use `set J : Ideal (Localization S) := Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} with hJ`. Establish `hIJ : Ideal.span {a : D | x * a = 0} ≤ J.comap (algebraMap D (Localization S))`. Rewrite using `[Ideal.span_le]`. Introduce `a ha`.

Use `show algebraMap D (Localization S) a ∈ J`. Apply `Ideal.subset_span` to reduce the goal to its premises. Use `show algebraMap D (Localization S) x * algebraMap D (Localization S) a = 0`. Rewrite using `[← map_mul, show x * a = 0 from ha, map_zero]`. Establish `key : Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N) ≤ ((J • (⊤ : Submodule (Localization S) (LocalizedModule S N))).restrictScalars D).comap (LocalizedModule.mkLinearMap S N)`.

Rewrite using `[Submodule.smul_le]`. Introduce `r hr m _`. Use `show LocalizedModule.mk (r • m) 1 ∈ J • (⊤ : Submodule (Localization S) (LocalizedModule S N))`. Rewrite using `[← LocalizedModule.smul'_mk, ← algebraMap_smul (Localization S) r]`. Conclude with `Submodule.smul_mem_smul (hIJ hr) trivial`.

Proceed by induction on `n using LocalizedModule.induction_on with`. Consider the case `_ m s`. Rewrite `hn` using `[algebraMap_smul (Localization S) x, LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `hn`. Simplify using `only [one_smul, smul_zero] at hu`.

Establish `hxu : x • (u • m) = 0` using `by rw [smul_comm]; exact hu`. Establish `hmem` using `key (h _ hxu)`. Establish `he : LocalizedModule.mk m s = (Localization.mk 1 (u * s) : Localization S) • LocalizedModule.mk (u • m) 1`. Rewrite using `[LocalizedModule.mk_smul_mk, one_smul, mul_one, LocalizedModule.mk_cancel_common_left]`. Rewrite using `[he]`.

Conclude with `Submodule.smul_mem _ _ hmem`.
-/
theorem localizedModule_mem_annSpan_smul_top (D : Type) [CommRing D] (S : Submonoid D) (x : D)
    (N : Type 1) [AddCommGroup N] [Module D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 →
      n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} •
        (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  intro n hn
  set J : Ideal (Localization S) :=
    Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} with hJ
  have hIJ : Ideal.span {a : D | x * a = 0} ≤ J.comap (algebraMap D (Localization S)) := by
    rw [Ideal.span_le]
    intro a ha
    show algebraMap D (Localization S) a ∈ J
    apply Ideal.subset_span
    show algebraMap D (Localization S) x * algebraMap D (Localization S) a = 0
    rw [← map_mul, show x * a = 0 from ha, map_zero]
  have key : Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N) ≤
      ((J • (⊤ : Submodule (Localization S) (LocalizedModule S N))).restrictScalars D).comap
        (LocalizedModule.mkLinearMap S N) := by
    rw [Submodule.smul_le]
    intro r hr m _
    show LocalizedModule.mk (r • m) 1 ∈ J • (⊤ : Submodule (Localization S) (LocalizedModule S N))
    rw [← LocalizedModule.smul'_mk, ← algebraMap_smul (Localization S) r]
    exact Submodule.smul_mem_smul (hIJ hr) trivial
  induction n using LocalizedModule.induction_on with
  | _ m s =>
    rw [algebraMap_smul (Localization S) x, LocalizedModule.smul'_mk,
      ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq] at hn
    obtain ⟨u, hu⟩ := hn
    simp only [one_smul, smul_zero] at hu
    have hxu : x • (u • m) = 0 := by rw [smul_comm]; exact hu
    have hmem := key (h _ hxu)
    have he : LocalizedModule.mk m s =
        (Localization.mk 1 (u * s) : Localization S) • LocalizedModule.mk (u • m) 1 := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, LocalizedModule.mk_cancel_common_left]
    rw [he]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory
