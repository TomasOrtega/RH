import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hne : Ideal.span {c} ≠ ⊥` using `by simpa using hc`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hp`. Establish `hm : IsLocalRing.maximalIdeal O = Ideal.span {p}` using `hp.maximalIdeal_eq`. Rewrite using `[hn, ← Ideal.span_singleton_pow, ← hm]`.

Use `haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := hF`. Conclude with `Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n`.
-/
theorem finite_quot_span_singleton_of_dvr_sandwich (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [hF : Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hp
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  rw [hn, ← Ideal.span_singleton_pow, ← hm]
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := hF
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

/- English proof (translation)
Introduce `O A _ _ _ _ _ _ C hC c hc`. Use `haveI := finite_quot_span_singleton_of_dvr_sandwich O c hc`. Use `haveI : Module.Finite O C := Module.Finite.iff_fg.mpr hC`. Set `K : Submodule O C` to `(Ideal.span {c}) • (⊤ : Submodule O C)`. Use `haveI : Finite (C ⧸ K) := Submodule.finite_quotient_smul (Ideal.span {c}) Module.Finite.fg_top`.

Set `f : Submodule O A → Set (C ⧸ K)` to `fun N => K.mkQ '' {x : C | (x : A) ∈ N}`. Establish `key : ∀ N M : Submodule O A, (N ≤ C ∧ ∀ x ∈ C, c • x ∈ N) → (M ≤ C ∧ ∀ x ∈ C, c • x ∈ M) → f N = f M → N ≤ M`. Introduce `N M hN hM h x hx`. Establish `h1 : K.mkQ ⟨x, hN.1 hx⟩ ∈ f M` using `h ▸ ⟨⟨x, hN.1 hx⟩, hx, rfl⟩`. Take `⟨y, hy, hxy⟩` from `h1`.

Establish `h2 : y - ⟨x, hN.1 hx⟩ ∈ K` using `(Submodule.Quotient.eq K).mp hxy`. Establish `h3 : ∀ z ∈ K, (z : A) ∈ M`. Introduce `z hz`. Use `Submodule.smul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `r hr n _`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Rewrite using `[Submodule.coe_smul, mul_smul]`. Conclude with `M.smul_mem a (hM.2 n n.2)`. Introduce `a b ha hb`. Conclude with `M.add_mem ha hb`.

Establish `h4` using `M.sub_mem hy (h3 _ h2)`. Simplify using `using h4`. Use `Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce `N hN M hM h`. Conclude with `le_antisymm (key N M hN hM h) (key M N hM hN h.symm)`.
-/
theorem finite_submodules_between_smul_and_self :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  intro O A _ _ _ _ _ _ C hC c hc
  haveI := finite_quot_span_singleton_of_dvr_sandwich O c hc
  haveI : Module.Finite O C := Module.Finite.iff_fg.mpr hC
  let K : Submodule O C := (Ideal.span {c}) • (⊤ : Submodule O C)
  haveI : Finite (C ⧸ K) := Submodule.finite_quotient_smul (Ideal.span {c}) Module.Finite.fg_top
  let f : Submodule O A → Set (C ⧸ K) := fun N => K.mkQ '' {x : C | (x : A) ∈ N}
  have key : ∀ N M : Submodule O A, (N ≤ C ∧ ∀ x ∈ C, c • x ∈ N) → (M ≤ C ∧ ∀ x ∈ C, c • x ∈ M) →
      f N = f M → N ≤ M := by
    intro N M hN hM h x hx
    have h1 : K.mkQ ⟨x, hN.1 hx⟩ ∈ f M := h ▸ ⟨⟨x, hN.1 hx⟩, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h1
    have h2 : y - ⟨x, hN.1 hx⟩ ∈ K := (Submodule.Quotient.eq K).mp hxy
    have h3 : ∀ z ∈ K, (z : A) ∈ M := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [Submodule.coe_smul, mul_smul]
        exact M.smul_mem a (hM.2 n n.2)
      · intro a b ha hb
        exact M.add_mem ha hb
    have h4 := M.sub_mem hy (h3 _ h2)
    simpa using h4
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro N hN M hM h
  exact le_antisymm (key N M hN hM h) (key M N hM hN h.symm)

end GlobalTheory
