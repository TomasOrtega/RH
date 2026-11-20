import Mathlib
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hJ` to reduce the goal to its premises. Rewrite using `[FractionalIdeal.eq_zero_iff]`.

Introduce `t ht`. Establish `h1` using `hspan t ht`. Establish `h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨z, hz, w, hw, rfl⟩`.

Conclude with `hcon z hz w hw`. Rewrite `h1` using `[h2]`. Conclude with `(Submodule.mem_bot _).1 h1`. Establish `hli : LinearIndependent F ![x, x']`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `e1 : B (s • x + t • x') x' = 0` using `by rw [hst]; simp`. Establish `e2 : B x (s • x + t • x') = 0` using `by rw [hst]; simp`. Simplify using `[hB, hxx] at e1 e2`. Conclude with `⟨e1, e2⟩`.

Establish `htop` using `hli.span_eq_top_of_card_eq_finrank (by simp [hV])`. Establish `hvm : v ∈ Submodule.span F ({x, x'} : Set V)`. Establish `: Set.range ![x, x'] = {x, x'}` using `by simp [Set.pair_comm]`. Rewrite using `[← this, htop]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨c, c', hc⟩` from `Submodule.mem_span_pair.1 hvm`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ ∀ a : F, a • v ∈ L → a * t ∈ J := by`. Distinguish the cases in `hc0 : c = 0`. Establish `hc' : c' ≠ 0`. Introduce and unpack `rfl`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[← hc, hc0]`. Simplify using the standard rewrite rules. Use `⟨B x v, ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`.

Simplify using `[hB, hxx, hc']`. Simplify using `using hBJ x hx _ ha`. Use `⟨B v x', ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Simplify using `[hB, hxx, hc0]`.

Simplify using `using hBJ _ ha x' hx'`. Set `M : Submodule (𝓞 F) F` to `{ carrier := {a | a • v ∈ L} add_mem' := fun {a b} ha hb => by show (a + b) • v ∈ L`. Rewrite using `[add_smul]`. Conclude with `hadd _ ha _ hb`. Use the proof step `zero_mem' := by show (0 : F) • v ∈ L`.

Rewrite using `[zero_smul]`. Conclude with `h0`. Use the proof step `smul_mem' := fun r a ha => by show ((r : F) * a) • v ∈ L`. Rewrite using `[mul_smul]`. Conclude with `hsmul r _ ha }`.

Establish `hM : IsFractional (𝓞 F)⁰ M`. Apply `FractionalIdeal.isFractional_of_le (J := FractionalIdeal.spanSingleton (𝓞 F)⁰ t⁻¹ * J)` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]`. Conclude with `⟨a * t, ht a ha, by field_simp⟩`.

Use `⟨⟨M, hM⟩, ?_, fun a => Iff.rfl⟩` and prove the remaining obligations. Take `⟨d, n, hn⟩` from `IsLocalization.exists_integer_multiple (𝓞 F)⁰ c`. Take `⟨d', n', hn'⟩` from `IsLocalization.exists_integer_multiple (𝓞 F)⁰ c'`. Establish `hn1 : (n : F) = ((d : 𝓞 F) : F) * c`. Simplify `hn` using `[Algebra.smul_def]`.

Establish `hn2 : (n' : F) = ((d' : 𝓞 F) : F) * c'`. Simplify `hn'` using `[Algebra.smul_def]`. Introduce `hz`. Use `replace hz := FractionalIdeal.eq_zero_iff.1 hz`. Establish `hmem : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v ∈ L`.

Establish `e : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v = ((d' : 𝓞 F) : F) • (n : F) • x + ((d : 𝓞 F) : F) • (n' : F) • x'`. Rewrite using `[← hc, hn1, hn2]`. Use `module`. Rewrite using `[e]`. Conclude with `hadd _ (hsmul _ _ (hsmul _ _ hx)) _ (hsmul _ _ (hsmul _ _ hx'))`.

Establish `h` using `hz _ hmem`. Establish `hd : ((d : 𝓞 F) : F) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero d`. Establish `hd' : ((d' : 𝓞 F) : F) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero d'`. Conclude with `mul_ne_zero hd hd' h`.
-/
theorem exists_fractionalIdeal_smul_mem_lattice_of_alternating
    {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    (L : Set V) (h0 : (0 : V) ∈ L) (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hBJ : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hspan t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨z, hz, w, hw, rfl⟩
      exact hcon z hz w hw
    rw [h2] at h1
    exact (Submodule.mem_bot _).1 h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : B (s • x + t • x') x' = 0 := by rw [hst]; simp
    have e2 : B x (s • x + t • x') = 0 := by rw [hst]; simp
    simp [hB, hxx] at e1 e2
    exact ⟨e1, e2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hvm : v ∈ Submodule.span F ({x, x'} : Set V) := by
    have : Set.range ![x, x'] = {x, x'} := by simp [Set.pair_comm]
    rw [← this, htop]; trivial
  obtain ⟨c, c', hc⟩ := Submodule.mem_span_pair.1 hvm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ ∀ a : F, a • v ∈ L → a * t ∈ J := by
    by_cases hc0 : c = 0
    · have hc' : c' ≠ 0 := by
        rintro rfl
        apply hv
        rw [← hc, hc0]; simp
      refine ⟨B x v, ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc']
      · simpa using hBJ x hx _ ha
    · refine ⟨B v x', ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc0]
      · simpa using hBJ _ ha x' hx'
  let M : Submodule (𝓞 F) F :=
    { carrier := {a | a • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • v ∈ L
        rw [add_smul]; exact hadd _ ha _ hb
      zero_mem' := by
        show (0 : F) • v ∈ L
        rw [zero_smul]; exact h0
      smul_mem' := fun r a ha => by
        show ((r : F) * a) • v ∈ L
        rw [mul_smul]; exact hsmul r _ ha }
  have hM : IsFractional (𝓞 F)⁰ M := by
    apply FractionalIdeal.isFractional_of_le
      (J := FractionalIdeal.spanSingleton (𝓞 F)⁰ t⁻¹ * J)
    intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    exact ⟨a * t, ht a ha, by field_simp⟩
  refine ⟨⟨M, hM⟩, ?_, fun a => Iff.rfl⟩
  obtain ⟨d, n, hn⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c
  obtain ⟨d', n', hn'⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c'
  have hn1 : (n : F) = ((d : 𝓞 F) : F) * c := by
    simpa [Algebra.smul_def] using hn
  have hn2 : (n' : F) = ((d' : 𝓞 F) : F) * c' := by
    simpa [Algebra.smul_def] using hn'
  intro hz
  replace hz := FractionalIdeal.eq_zero_iff.1 hz
  have hmem : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v ∈ L := by
    have e : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v
        = ((d' : 𝓞 F) : F) • (n : F) • x + ((d : 𝓞 F) : F) • (n' : F) • x' := by
      rw [← hc, hn1, hn2]; module
    rw [e]
    exact hadd _ (hsmul _ _ (hsmul _ _ hx)) _ (hsmul _ _ (hsmul _ _ hx'))
  have h := hz _ hmem
  have hd : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hd' : ((d' : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d'
  exact mul_ne_zero hd hd' h

end GlobalTheory
