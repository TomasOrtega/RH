import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

open NumberField in
open scoped nonZeroDivisors in
/- English proof (translation)
Use `set Af : FractionalIdeal (𝓞 E)⁰ E := ⟨A, FractionalIdeal.isFractional_of_fg hA⟩ with hAf`. Establish `hne : Af ≠ 0`. Introduce `h`. Establish `: (1 : E) ∈ Af` using `h1`. Rewrite `this` using `[h, FractionalIdeal.mem_zero_iff]`.

Conclude with `one_ne_zero this`. Establish `hmem : (1 : E) ∈ ((Af * Af⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)`. Rewrite using `[mul_inv_cancel₀ hne]`. Conclude with `FractionalIdeal.one_mem_one _`. Rewrite `hmem` using `[FractionalIdeal.coe_mul]`.

Use `Submodule.mul_induction_on hmem (fun a ha x hx => ?_) (fun _ _ => add_mem)` and prove the remaining obligations. Establish `hinv : ∀ y ∈ A, x * y ∈ (1 : Submodule (𝓞 E) E)`. Introduce `y hy`. Use `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp hx) (show y ∈ Af from hy)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel₀ hne]`.

Rewrite `this` using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]`. Conclude with `this`. Take `⟨i, rfl⟩` from `Submodule.mem_one.mp (by simpa using hinv 1 h1)`. Establish `hi : i ∈ (1 : Submodule (𝓞 E) E).colon (A : Set E)`. Rewrite using `[Submodule.mem_colon]`.

Introduce `s hs`. Rewrite using `[Algebra.smul_def]`. Conclude with `hinv s hs`. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem_smul hi ha`.
-/
private theorem one_mem_colon_one_smul_of_fg {E : Type} [Field E] [NumberField E]
    (A : Submodule (𝓞 E) E) (hA : A.FG) (h1 : (1 : E) ∈ A) :
    (1 : E) ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A := by
  set Af : FractionalIdeal (𝓞 E)⁰ E := ⟨A, FractionalIdeal.isFractional_of_fg hA⟩ with hAf
  have hne : Af ≠ 0 := by
    intro h
    have : (1 : E) ∈ Af := h1
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  have hmem : (1 : E) ∈ ((Af * Af⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    rw [mul_inv_cancel₀ hne]; exact FractionalIdeal.one_mem_one _
  rw [FractionalIdeal.coe_mul] at hmem
  refine Submodule.mul_induction_on hmem (fun a ha x hx => ?_) (fun _ _ => add_mem)
  have hinv : ∀ y ∈ A, x * y ∈ (1 : Submodule (𝓞 E) E) := by
    intro y hy
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp hx) (show y ∈ Af from hy)
    rw [inv_mul_cancel₀ hne] at this
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at this
    exact this
  obtain ⟨i, rfl⟩ := Submodule.mem_one.mp (by simpa using hinv 1 h1)
  have hi : i ∈ (1 : Submodule (𝓞 E) E).colon (A : Set E) := by
    rw [Submodule.mem_colon]
    intro s hs
    rw [Algebra.smul_def]
    exact hinv s hs
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem_smul hi ha

open NumberField in
open scoped nonZeroDivisors in

/- English proof (translation)
Establish `key` using `one_mem_colon_one_smul_of_fg A hA h1`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `r hr`. Rewrite `hr` using `[Submodule.mem_colon]`. Establish `hb : ∀ a ∈ A, ∃ u : 𝓞 K, (u : K) = (r : K) * τE a`.

Introduce `a ha`. Take `⟨u, hu⟩` from `Submodule.mem_one.mp (hr _ (Submodule.subset_span ⟨a, ha, rfl⟩))`. Rewrite `hu` using `[Algebra.smul_def]`. Conclude with `⟨u, hu⟩`. Establish `hP : ∀ x ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A, ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ, (t : K) = (r : K) * τE x`.

Introduce `x hx`. Use `Submodule.smul_induction_on (p := fun x => ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ, (t : K) = (r : K) * τE x) hx (fun i hi a ha => ?_) ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `hb a ha`. Use `⟨τ i * u, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem τ hi), ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`.

Express the relevant statement in the definitionally equal form `((τ i : 𝓞 K) : K) * (u : K) = (r : K) * (τE (i : E) * τE a)`. Rewrite using `[hu, hτ]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `x y ⟨t, ht, hte⟩ ⟨t', ht', hte'⟩`. Use `⟨t + t', add_mem ht ht', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, mul_add, ← hte, ← hte']`. Both sides reduce to the same expression. Take `⟨t, ht, hte⟩` from `hP 1 key`. Rewrite `hte` using `[map_one, mul_one]`. Establish `htr : t = r` using `by exact_mod_cast hte`.

Rewrite using `[← htr]` and apply the resulting hypothesis. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `i hi`. Rewrite using `[Ideal.mem_comap, Submodule.mem_colon]`. Introduce `s hs`.

Rewrite `hs` using `[SetLike.mem_coe]`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem s hs`. Take `⟨a, ha, rfl⟩` from `hs`. Take `⟨y, hy⟩` from `Submodule.mem_one.mp ((Submodule.mem_colon.mp hi) a ha)`.

Use `Submodule.mem_one.mpr ⟨τ y, ?_⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `(y : E) = (i : E) * a at hy`. Express the relevant statement in the definitionally equal form `((τ y : 𝓞 K) : K) = ((τ i : 𝓞 K) : K) * τE a`. Rewrite using `[← hτ, ← hτ, hy, map_mul]`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem _root_.GlobalTheory.colon_one_span_image_eq_map {E K : Type} [Field E] [NumberField E] [Field K]
    [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K))
    (A : Submodule (𝓞 E) E) (hA : A.FG) (h1 : (1 : E) ∈ A) :
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  have key := one_mem_colon_one_smul_of_fg A hA h1
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_colon] at hr
    have hb : ∀ a ∈ A, ∃ u : 𝓞 K, (u : K) = (r : K) * τE a := by
      intro a ha
      obtain ⟨u, hu⟩ := Submodule.mem_one.mp (hr _ (Submodule.subset_span ⟨a, ha, rfl⟩))
      rw [Algebra.smul_def] at hu
      exact ⟨u, hu⟩
    have hP : ∀ x ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)) • A,
        ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ, (t : K) = (r : K) * τE x := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x => ∃ t ∈ ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ,
          (t : K) = (r : K) * τE x) hx (fun i hi a ha => ?_) ?_
      · obtain ⟨u, hu⟩ := hb a ha
        refine ⟨τ i * u, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem τ hi), ?_⟩
        rw [Algebra.smul_def, map_mul]
        change ((τ i : 𝓞 K) : K) * (u : K) = (r : K) * (τE (i : E) * τE a)
        rw [hu, hτ]
        ring
      · rintro x y ⟨t, ht, hte⟩ ⟨t', ht', hte'⟩
        refine ⟨t + t', add_mem ht ht', ?_⟩
        rw [map_add, mul_add, ← hte, ← hte']
        rfl
    obtain ⟨t, ht, hte⟩ := hP 1 key
    rw [map_one, mul_one] at hte
    have htr : t = r := by exact_mod_cast hte
    rwa [← htr]
  · rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s hs
    rw [SetLike.mem_coe] at hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha, rfl⟩ := hs
      obtain ⟨y, hy⟩ := Submodule.mem_one.mp ((Submodule.mem_colon.mp hi) a ha)
      refine Submodule.mem_one.mpr ⟨τ y, ?_⟩
      rw [Algebra.smul_def] at hy ⊢
      change (y : E) = (i : E) * a at hy
      change ((τ y : 𝓞 K) : K) = ((τ i : 𝓞 K) : K) * τE a
      rw [← hτ, ← hτ, hy, map_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

end GlobalTheory
