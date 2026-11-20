import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StModelLocalizationMaximalPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

/- English proof (translation)
Introduce `n J q M P hP`. Set `A` to `MvPolynomial (Fin n) ℂ`. Set `R'` to `MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal`. Set `L` to `Localization (normalModelSubmonoid M q)`. Set `ι : A →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ` to `(rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom`.

Set `φ : A →+* R'` to `(Ideal.Quotient.mk M.ideal).comp ι`. Set `_ : Algebra A R'` to `φ.toAlgebra`. Establish `hφ : ∀ f : A, algebraMap A R' f = Ideal.Quotient.mk M.ideal (rename Sum.inl f)` using `fun _ ↦ rfl`. Establish `hint : Algebra.IsIntegral A R'`. Prove the components needed by the constructor for the conclusion.

Introduce `x`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c`. Establish `h : algebraMap A R' (C c) = Ideal.Quotient.mk M.ideal (C c)` using `by rw [hφ, rename_C]`.

Conclude with `h ▸ isIntegral_algebraMap`. Consider the case `add p r hp hr => rw [map_add]`. Conclude with `hp.add hr`. Consider the case `mul_X p s hp`. Rewrite using `[map_mul]`.

Use `hp.mul ?_` and prove the remaining obligations. Consider the cases of `s with`. Consider the case `inl i`. Establish `h : algebraMap A R' (X i) = Ideal.Quotient.mk M.ideal (X (Sum.inl i))` using `by rw [hφ, rename_X]`. Conclude with `h ▸ isIntegral_algebraMap`.

Consider the case `inr i`. Take `⟨F, hmon, hF⟩` from `M.integral i`. Use `⟨F, hmon, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.algebraMap_toAlgebra, show φ = (Ideal.Quotient.mk M.ideal).comp ι from rfl, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hF`.

Set `m : Ideal A` to `RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)`. Establish `hm : m.IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩`. Set `Q : Ideal R'` to `P.comap (algebraMap R' L)`. Establish `hQm : Q.comap (algebraMap A R') ≤ m`. Introduce `f hf`.

Assume the negation of the conclusion as `hfm`. Establish `hS : algebraMap A R' f ∈ normalModelSubmonoid M q` using `Submonoid.mem_map_of_mem _ hfm`. Conclude with `hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.map_units L ⟨_, hS⟩))`. Take `⟨Q', hQQ', hQ'prime, hQ'm⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral m Q hQm`. Establish `hdisj : Disjoint (normalModelSubmonoid M q : Set R') Q'`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨f, hf, rfl⟩ hfQ`. Apply `hf` to reduce the goal to its premises. Establish `h : f ∈ Q'.comap (algebraMap A R')` using `hfQ`. Rewrite `h` using `[hQ'm]`.

Conclude with `h`. Establish `hPQ' : P = Q'.map (algebraMap R' L)`. Establish `hne : Q'.map (algebraMap R' L) ≠ ⊤` using `(IsLocalization.isPrime_of_isPrime_disjoint (normalModelSubmonoid M q) L Q' hQ'prime hdisj).ne_top`. Use `hP.eq_of_le hne ?_` and prove the remaining obligations. Rewrite using `[← IsLocalization.map_under (normalModelSubmonoid M q) L P]`.

Conclude with `Ideal.map_mono hQQ'`. Establish `hQeq : P.comap (algebraMap R' L) = Q'`. Rewrite using `[hPQ']`. Conclude with `IsLocalization.under_map_of_isPrime_disjoint (normalModelSubmonoid M q) L hQ'prime hdisj`. Establish `hQ'max : Q'.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q' (hQ'm ▸ hm)`.

Set `N` to `P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))`. Establish `hNmax : N.IsMaximal` using `by show (P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))).IsMaximal`. Rewrite using `[← Ideal.comap_comap, hQeq]`. Conclude with `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨w, hw⟩` from `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hNmax`.

Establish `key : ∀ p, p ∈ N ↔ eval w p = 0` using `fun p ↦ by`. Rewrite using `[hw, mem_vanishingIdeal_singleton_iff]`. Conclude with `Iff.rfl`. Use `⟨w, fun p hp ↦ (key p).1 ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap R' L (Ideal.Quotient.mk M.ideal p) ∈ P`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]`. Conclude with `P.zero_mem`. Use function extensionality and compare the values at `i`. Establish `h1 : X i - C (q i) ∈ m` using `by show eval q (X i - C (q i)) = 0`. Rewrite using `[map_sub, eval_X, eval_C, sub_self]`.

Rewrite `h1` using `[← hQ'm, ← hQeq]`. Establish `h2` using `(key (rename Sum.inl (X i - C (q i)))).1 h1`. Simplify using `only [map_sub, rename_X, rename_C, eval_X, eval_C] at h2`. Conclude with `sub_eq_zero.1 h2`. Use extensionality with `p`.

Rewrite using `[RingHom.mem_ker]`. Conclude with `key p`.
-/
theorem ModelLocalizationMaximalPoint.proof : ModelLocalizationMaximalPoint.Statement := by
  intro n J q M P hP
  let A := MvPolynomial (Fin n) ℂ
  let R' := MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal
  let L := Localization (normalModelSubmonoid M q)
  let ι : A →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
  let φ : A →+* R' := (Ideal.Quotient.mk M.ideal).comp ι
  let _ : Algebra A R' := φ.toAlgebra
  have hφ : ∀ f : A, algebraMap A R' f = Ideal.Quotient.mk M.ideal (rename Sum.inl f) := fun _ ↦ rfl

  have hint : Algebra.IsIntegral A R' := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h : algebraMap A R' (C c) = Ideal.Quotient.mk M.ideal (C c) := by rw [hφ, rename_C]
      exact h ▸ isIntegral_algebraMap
    | add p r hp hr => rw [map_add]; exact hp.add hr
    | mul_X p s hp =>
      rw [map_mul]
      refine hp.mul ?_
      cases s with
      | inl i =>
        have h : algebraMap A R' (X i) = Ideal.Quotient.mk M.ideal (X (Sum.inl i)) := by rw [hφ, rename_X]
        exact h ▸ isIntegral_algebraMap
      | inr i =>
        obtain ⟨F, hmon, hF⟩ := M.integral i
        refine ⟨F, hmon, ?_⟩
        rw [RingHom.algebraMap_toAlgebra, show φ = (Ideal.Quotient.mk M.ideal).comp ι from rfl,
          ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hF

  let m : Ideal A := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩
  let Q : Ideal R' := P.comap (algebraMap R' L)
  have hQm : Q.comap (algebraMap A R') ≤ m := by
    intro f hf
    by_contra hfm
    have hS : algebraMap A R' f ∈ normalModelSubmonoid M q := Submonoid.mem_map_of_mem _ hfm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.map_units L ⟨_, hS⟩))

  obtain ⟨Q', hQQ', hQ'prime, hQ'm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m Q hQm
  have hdisj : Disjoint (normalModelSubmonoid M q : Set R') Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, hf, rfl⟩ hfQ
    apply hf
    have h : f ∈ Q'.comap (algebraMap A R') := hfQ
    rw [hQ'm] at h
    exact h
  have hPQ' : P = Q'.map (algebraMap R' L) := by
    have hne : Q'.map (algebraMap R' L) ≠ ⊤ :=
      (IsLocalization.isPrime_of_isPrime_disjoint (normalModelSubmonoid M q) L Q' hQ'prime hdisj).ne_top
    refine hP.eq_of_le hne ?_
    rw [← IsLocalization.map_under (normalModelSubmonoid M q) L P]
    exact Ideal.map_mono hQQ'
  have hQeq : P.comap (algebraMap R' L) = Q' := by
    rw [hPQ']
    exact IsLocalization.under_map_of_isPrime_disjoint (normalModelSubmonoid M q) L hQ'prime hdisj
  have hQ'max : Q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q' (hQ'm ▸ hm)

  let N := P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))
  have hNmax : N.IsMaximal := by
    show (P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))).IsMaximal
    rw [← Ideal.comap_comap, hQeq]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hNmax
  have key : ∀ p, p ∈ N ↔ eval w p = 0 := fun p ↦ by
    rw [hw, mem_vanishingIdeal_singleton_iff]
    exact Iff.rfl
  refine ⟨w, fun p hp ↦ (key p).1 ?_, ?_, ?_⟩
  · show algebraMap R' L (Ideal.Quotient.mk M.ideal p) ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    exact P.zero_mem
  · funext i
    have h1 : X i - C (q i) ∈ m := by
      show eval q (X i - C (q i)) = 0
      rw [map_sub, eval_X, eval_C, sub_self]
    rw [← hQ'm, ← hQeq] at h1
    have h2 := (key (rename Sum.inl (X i - C (q i)))).1 h1
    simp only [map_sub, rename_X, rename_C, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  · ext p
    rw [RingHom.mem_ker]
    exact key p

end

end GroundTheory.Heights₂.Heights
