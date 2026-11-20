import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `k H _ _ _ _ _ C hC E`. Take `⟨s0, hs0⟩` from `Module.projective_lifting_property C.mkQ E.subtype (Submodule.mkQ_surjective C)`. Establish `hsec : ∀ (s : E →ₗ[k] H), C.mkQ ∘ₗ s = E.subtype → ∀ e : E, C.mkQ (s e) = e`. Introduce `s hs e`. Conclude with `LinearMap.congr_fun hs e`.

Set `S` to `{s : E →ₗ[k] H // C.mkQ ∘ₗ s = E.subtype}`. Establish `hF : ∀ s : S, ¬C ≤ LinearMap.range s.1 ∧ Submodule.map C.mkQ (LinearMap.range s.1) = E`. Introduce `s`. Prove the components needed by the constructor for the conclusion. Introduce `hle haveI : Nontrivial C := Module.nontrivial_of_finrank_eq_succ hC`.

Take `⟨c, hc⟩` from `exists_ne (0 : C)`. Take `⟨e, he⟩` from `LinearMap.mem_range.1 (hle c.2)`. Establish `h1 : C.mkQ (s.1 e) = e` using `hsec s.1 s.2 e`. Establish `h2 : C.mkQ (c : H) = 0` using `(Submodule.Quotient.mk_eq_zero C).2 c.2`. Rewrite `h1` using `[he, h2]`.

Establish `e0 : e = 0` using `Subtype.ext h1.symm`. Apply `hc` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← he, e0, map_zero]`. Both sides reduce to the same expression.

Rewrite using `[← LinearMap.range_comp, s.2, Submodule.range_subtype]`. Set `F : S → {D : Submodule k H // ¬C ≤ D ∧ Submodule.map C.mkQ D = E}` to `fun s => ⟨LinearMap.range s.1, hF s⟩`. Establish `hFb : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce `s t h`.

Establish `h' : LinearMap.range s.1 = LinearMap.range t.1` using `congrArg Subtype.val h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `e`. Establish `hm : s.1 e ∈ LinearMap.range t.1` using `h' ▸ LinearMap.mem_range_self s.1 e`.

Take `⟨e', he'⟩` from `LinearMap.mem_range.1 hm`. Establish `h1` using `hsec t.1 t.2 e'`. Rewrite `h1` using `[he', hsec s.1 s.2 e]`. Establish `: e' = e` using `Subtype.ext h1.symm`. Rewrite using `[← he', this]`.

Introduce and unpack `⟨D, hnot, hmap⟩`. Establish `hdisj : ∀ x ∈ D, x ∈ C → x = 0`. Introduce `x hxD hxC`. Assume the negation of the conclusion as `hx`. Apply `hnot` to reduce the goal to its premises.

Introduce `y hy`. Establish `hx' : (⟨x, hxC⟩ : C) ≠ 0` using `fun h => hx (congrArg Subtype.val h)`. Take `⟨a, ha⟩` from `(finrank_eq_one_iff_of_nonzero' _ hx').1 hC ⟨y, hy⟩`. Establish `: a • x = y` using `congrArg Subtype.val ha`. Rewrite using `[← this]`.

Conclude with `D.smul_mem a hxD`. Set `f : D →ₗ[k] H ⧸ C` to `C.mkQ ∘ₗ D.subtype`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `d hd`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hdisj d.1 d.2 ((Submodule.Quotient.mk_eq_zero C).1 hd)`. Establish `hr : LinearMap.range f = E`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype, hmap]`. Set `φ : D ≃ₗ[k] E` to `(LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)`.

Establish `hφ : ∀ d : D, ((φ d : E) : H ⧸ C) = C.mkQ d` using `fun d => rfl`. Set `s : E →ₗ[k] H` to `D.subtype ∘ₗ (φ.symm : E →ₗ[k] D)`. Establish `hs : C.mkQ ∘ₗ s = E.subtype`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `e`.

Establish `h1` using `hφ (φ.symm e)`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1.symm`. Use `⟨⟨s, hs⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show LinearMap.range s = D`.

Rewrite using `[LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.symm), Submodule.range_subtype]`. Set `G : (E →ₗ[k] C) → S` to `fun g => ⟨s0 + C.subtype ∘ₗ g, by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `e`. Establish `h1` using `LinearMap.congr_fun hs0 e`.

Establish `h2 : C.mkQ (g e : H) = 0` using `(Submodule.Quotient.mk_eq_zero C).2 (g e).2`. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Submodule.subtype_apply] at h1 ⊢`. Rewrite using `[h2, add_zero, h1]⟩`. Establish `hGb : Function.Bijective G`. Prove the components needed by the constructor for the conclusion.

Introduce `g g' h`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `e`. Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.congr_fun (congrArg Subtype.val h) e` as an intermediate fact.

Simplify `this` using `[G]`. Introduce and unpack `⟨s, hs⟩`. Establish `hmem : ∀ e, s e - s0 e ∈ C`. Introduce `e`. Apply `(Submodule.Quotient.mk_eq_zero C).1` to reduce the goal to its premises.

Establish `h1` using `hsec s hs e`. Establish `h2` using `hsec s0 hs0 e`. Simplify using `only [Submodule.mkQ_apply] at h1 h2`. Rewrite using `[Submodule.Quotient.mk_sub, h1, h2, sub_self]`. Use `⟨LinearMap.codRestrict C (s - s0) hmem, Subtype.ext ?_⟩` and prove the remaining obligations.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `e`. Simplify using `[G]`. Establish `hcard : Nat.card (E →ₗ[k] C) = Nat.card k ^ Module.finrank k E` using `by haveI : Fintype k := Fintype.ofFinite k haveI : Finite (E →ₗ[k] C) := Module.finite_of_finite k haveI : Fintype (E →ₗ[k] C) := Fintype.ofFinite _`. Rewrite using `[Nat.card_eq_fintype_card (α := E →ₗ[k] C), Nat.card_eq_fintype_card (α := k), Module.card_eq_pow_finrank (K := k) (V := E →ₗ[k] C), Module.finrank_linearMap k k E C, hC, mul_one]`.

Rewrite using `[← Nat.card_eq_of_bijective F hFb, ← Nat.card_eq_of_bijective G hGb, hcard]`.
-/
theorem countOut_of : CountOut := by
  intro k H _ _ _ _ _ C hC E
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property C.mkQ E.subtype (Submodule.mkQ_surjective C)
  have hsec : ∀ (s : E →ₗ[k] H), C.mkQ ∘ₗ s = E.subtype → ∀ e : E, C.mkQ (s e) = e := by
    intro s hs e
    exact LinearMap.congr_fun hs e
  let S := {s : E →ₗ[k] H // C.mkQ ∘ₗ s = E.subtype}
  have hF : ∀ s : S, ¬C ≤ LinearMap.range s.1 ∧ Submodule.map C.mkQ (LinearMap.range s.1) = E := by
    intro s
    constructor
    · intro hle
      haveI : Nontrivial C := Module.nontrivial_of_finrank_eq_succ hC
      obtain ⟨c, hc⟩ := exists_ne (0 : C)
      obtain ⟨e, he⟩ := LinearMap.mem_range.1 (hle c.2)
      have h1 : C.mkQ (s.1 e) = e := hsec s.1 s.2 e
      have h2 : C.mkQ (c : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 c.2
      rw [he, h2] at h1
      have e0 : e = 0 := Subtype.ext h1.symm
      apply hc
      apply Subtype.ext
      rw [← he, e0, map_zero]
      rfl
    · rw [← LinearMap.range_comp, s.2, Submodule.range_subtype]
  let F : S → {D : Submodule k H // ¬C ≤ D ∧ Submodule.map C.mkQ D = E} :=
    fun s => ⟨LinearMap.range s.1, hF s⟩
  have hFb : Function.Bijective F := by
    constructor
    · intro s t h
      have h' : LinearMap.range s.1 = LinearMap.range t.1 := congrArg Subtype.val h
      apply Subtype.ext
      apply LinearMap.ext
      intro e
      have hm : s.1 e ∈ LinearMap.range t.1 := h' ▸ LinearMap.mem_range_self s.1 e
      obtain ⟨e', he'⟩ := LinearMap.mem_range.1 hm
      have h1 := hsec t.1 t.2 e'
      rw [he', hsec s.1 s.2 e] at h1
      have : e' = e := Subtype.ext h1.symm
      rw [← he', this]
    · rintro ⟨D, hnot, hmap⟩
      have hdisj : ∀ x ∈ D, x ∈ C → x = 0 := by
        intro x hxD hxC
        by_contra hx
        apply hnot
        intro y hy
        have hx' : (⟨x, hxC⟩ : C) ≠ 0 := fun h => hx (congrArg Subtype.val h)
        obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').1 hC ⟨y, hy⟩
        have : a • x = y := congrArg Subtype.val ha
        rw [← this]
        exact D.smul_mem a hxD
      let f : D →ₗ[k] H ⧸ C := C.mkQ ∘ₗ D.subtype
      have hf : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro d hd
        apply Subtype.ext
        exact hdisj d.1 d.2 ((Submodule.Quotient.mk_eq_zero C).1 hd)
      have hr : LinearMap.range f = E := by
        rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
      let φ : D ≃ₗ[k] E := (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)
      have hφ : ∀ d : D, ((φ d : E) : H ⧸ C) = C.mkQ d := fun d => rfl
      let s : E →ₗ[k] H := D.subtype ∘ₗ (φ.symm : E →ₗ[k] D)
      have hs : C.mkQ ∘ₗ s = E.subtype := by
        apply LinearMap.ext
        intro e
        have h1 := hφ (φ.symm e)
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      show LinearMap.range s = D
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.symm), Submodule.range_subtype]
  let G : (E →ₗ[k] C) → S := fun g =>
    ⟨s0 + C.subtype ∘ₗ g, by
      apply LinearMap.ext
      intro e
      have h1 := LinearMap.congr_fun hs0 e
      have h2 : C.mkQ (g e : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 (g e).2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Submodule.subtype_apply] at h1 ⊢
      rw [h2, add_zero, h1]⟩
  have hGb : Function.Bijective G := by
    constructor
    · intro g g' h
      apply LinearMap.ext
      intro e
      apply Subtype.ext
      have := LinearMap.congr_fun (congrArg Subtype.val h) e
      simpa [G] using this
    · rintro ⟨s, hs⟩
      have hmem : ∀ e, s e - s0 e ∈ C := by
        intro e
        apply (Submodule.Quotient.mk_eq_zero C).1
        have h1 := hsec s hs e
        have h2 := hsec s0 hs0 e
        simp only [Submodule.mkQ_apply] at h1 h2
        rw [Submodule.Quotient.mk_sub, h1, h2, sub_self]
      refine ⟨LinearMap.codRestrict C (s - s0) hmem, Subtype.ext ?_⟩
      apply LinearMap.ext
      intro e
      simp [G]
  have hcard : Nat.card (E →ₗ[k] C) = Nat.card k ^ Module.finrank k E := by
    haveI : Fintype k := Fintype.ofFinite k
    haveI : Finite (E →ₗ[k] C) := Module.finite_of_finite k
    haveI : Fintype (E →ₗ[k] C) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := E →ₗ[k] C), Nat.card_eq_fintype_card (α := k), Module.card_eq_pow_finrank (K := k) (V := E →ₗ[k] C),
      Module.finrank_linearMap k k E C, hC, mul_one]
  rw [← Nat.card_eq_of_bijective F hFb, ← Nat.card_eq_of_bijective G hGb, hcard]

end UpperTheory.Gal.crystallineComparison
