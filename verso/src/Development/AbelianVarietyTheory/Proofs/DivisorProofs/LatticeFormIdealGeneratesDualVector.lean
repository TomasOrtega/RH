import Mathlib

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Establish `hanti : B x' x = - B x x'`. Establish `h1` using `hB (x + x')`. Simplify using `only [map_add, LinearMap.add_apply, hB] at h1`. Take the linear combination `h1`. Establish `hli : LinearIndependent F ![x, x']`.

Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h1` using `congrArg (fun u => B u x') hst`. Establish `h2` using `congrArg (fun u => B x u) hst`. Simplify using `[hB] at h1 h2`.

Conclude with `⟨h1.resolve_right h, h2.resolve_right h⟩`. Establish `hsp : Submodule.span F (Set.range ![x, x']) = ⊤` using `hli.span_eq_top_of_card_eq_finrank (by simp [hV])`. Establish `hv : v ∈ Submodule.span F (Set.range ![x, x'])` using `by rw [hsp]; trivial`. Rewrite `hv` using `[Matrix.range_cons_cons_empty, Submodule.mem_span_pair]`. Take `⟨a, b, hab⟩` from `hv`.

Conclude with `⟨a, b, hab.symm⟩`.
-/
theorem exists_coords_of_alt_ne_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {x x' : V} (h : B x x' ≠ 0) (v : V) : ∃ c c' : F, v = c • x + c' • x' := by
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun u => B u x') hst
    have h2 := congrArg (fun u => B x u) hst
    simp [hB] at h1 h2
    exact ⟨h1.resolve_right h, h2.resolve_right h⟩
  have hsp : Submodule.span F (Set.range ![x, x']) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hv : v ∈ Submodule.span F (Set.range ![x, x']) := by rw [hsp]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hv
  obtain ⟨a, b, hab⟩ := hv
  exact ⟨a, b, hab.symm⟩

/- English proof (translation)
Introduce `F V _ _ _ _ hV B hB L h0 hadd hsmul J hJ hLJ hJL v hv`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hJ` to reduce the goal to its premises.

Rewrite using `[FractionalIdeal.eq_zero_iff]`. Introduce `t ht`. Establish `h1` using `hJL t ht`. Establish `h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} ≤ ⊥`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `s ⟨z, hz, w, hw, rfl⟩`. Simplify using `using hcon z hz w hw`. Simplify using `using h2 h1`. Take `⟨c, c', rfl⟩` from `exists_coords_of_alt_ne_zero hV B hB hxx v`. Set `M : Submodule (𝓞 F) F` to `{ carrier := {t | ∃ z ∈ L, t = B z (c • x + c' • x')} zero_mem' := ⟨0, h0, by simp⟩ add_mem' := by`.

Introduce and unpack `_ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩`. Conclude with `⟨z + w, hadd z hz w hw, by rw [map_add B, LinearMap.add_apply]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a _ ⟨z, hz, rfl⟩`. Use `⟨(a : F) • z, hsmul a z hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul B, LinearMap.smul_apply, Algebra.smul_def, smul_eq_mul] }`. Establish `hM : M ≤ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ c * J + FractionalIdeal.spanSingleton (𝓞 F)⁰ c' * J : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[FractionalIdeal.coe_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations.

Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hLJ z hz x hx)`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hLJ z hz x' hx')`. Use `⟨⟨M, FractionalIdeal.isFractional_of_le hM⟩, ?_, fun t => Iff.rfl⟩` and prove the remaining obligations. Introduce `hK0`. Establish `hK` using `FractionalIdeal.eq_zero_iff.1 hK0`.

Establish `h1` using `hK _ (show B x (c • x + c' • x') ∈ M from ⟨x, hx, rfl⟩)`. Establish `h2` using `hK _ (show B x' (c • x + c' • x') ∈ M from ⟨x', hx', rfl⟩)`. Establish `hanti : B x' x = - B x x'`. Establish `h1` using `hB (x + x')`. Simplify using `only [map_add, LinearMap.add_apply, hB] at h1`.

Take the linear combination `h1`. Simplify using `[hB, hanti, hxx] at h1 h2`. Apply `hv` to reduce the goal to its premises. Simplify using `[h1, h2]`.
-/
theorem exists_fractionalIdeal_pairing_values :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V],
    Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) →
    ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 →
      ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v := by
  intro F V _ _ _ _ hV B hB L h0 hadd hsmul J hJ hLJ hJL v hv
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hJL t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro s ⟨z, hz, w, hw, rfl⟩
      simpa using hcon z hz w hw
    simpa using h2 h1
  obtain ⟨c, c', rfl⟩ := exists_coords_of_alt_ne_zero hV B hB hxx v
  let M : Submodule (𝓞 F) F :=
    { carrier := {t | ∃ z ∈ L, t = B z (c • x + c' • x')}
      zero_mem' := ⟨0, h0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨z + w, hadd z hz w hw, by rw [map_add B, LinearMap.add_apply]⟩
      smul_mem' := by
        rintro a _ ⟨z, hz, rfl⟩
        refine ⟨(a : F) • z, hsmul a z hz, ?_⟩
        rw [map_smul B, LinearMap.smul_apply, Algebra.smul_def, smul_eq_mul] }
  have hM : M ≤ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ c * J +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ c' * J : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [FractionalIdeal.coe_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    refine Submodule.add_mem_sup ?_ ?_
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x hx)
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (hLJ z hz x' hx')
  refine ⟨⟨M, FractionalIdeal.isFractional_of_le hM⟩, ?_, fun t => Iff.rfl⟩
  intro hK0
  have hK := FractionalIdeal.eq_zero_iff.1 hK0
  have h1 := hK _ (show B x (c • x + c' • x') ∈ M from ⟨x, hx, rfl⟩)
  have h2 := hK _ (show B x' (c • x + c' • x') ∈ M from ⟨x', hx', rfl⟩)
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  simp [hB, hanti, hxx] at h1 h2
  apply hv
  simp [h1, h2]

end GlobalTheory
