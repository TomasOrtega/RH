import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

/- English proof (translation)
Establish `h : ofF b x u i = b.equivFun.symm (fun k => x (i, k))`. Simplify using `[ofF, Module.Basis.equivFun_symm_apply]`. Rewrite using `[h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem repr_ofF {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) (u : Fin 1) (i : Fin M) (k : Fin d) :
    b.repr (ofF b x u i) k = x (i, k) := by
  have h : ofF b x u i = b.equivFun.symm (fun k => x (i, k)) := by
    simp [ofF, Module.Basis.equivFun_symm_apply]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Use function extensionality and compare the values at `p`. Take `⟨i, k⟩` from `p`. Rewrite using `[← repr_ofF b x 0 i k, ← repr_ofF b y 0 i k, hxy]`.

Introduce `Y`. Use `⟨fun p => b.repr (Y 0 p.1) p.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u i`. Take `rfl : u = 0` from `Subsingleton.elim _ _`. Conclude with `b.sum_repr (Y 0 i)`.
-/
theorem ofF_bijective {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) := by
  constructor
  · intro x y hxy
    funext p
    obtain ⟨i, k⟩ := p
    rw [← repr_ofF b x 0 i k, ← repr_ofF b y 0 i k, hxy]
  · intro Y
    refine ⟨fun p => b.repr (Y 0 p.1) p.2, ?_⟩
    funext u i
    obtain rfl : u = 0 := Subsingleton.elim _ _
    exact b.sum_repr (Y 0 i)

/- English proof (translation)
Use function extensionality and compare the values at `u i`. Simplify using `[ofF]`.
-/
theorem ofF_zero {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    ofF b (0 : Fin M × Fin d → F) = 0 := by
  funext u i
  simp [ofF]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by omega)`. Establish `li : LinearIndependent F ![(1 : E), h]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Establish `ht : t = 0`. Assume the negation of the conclusion as `ht`. Apply `hcon (-(s / t))` to reduce the goal to its premises. Establish `h1 : algebraMap F E t * h = -algebraMap F E s`.

Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Take the linear combination `hst`. Establish `ht' : algebraMap F E t ≠ 0` using `by simpa using ht`. Rewrite using `[map_neg, map_div₀]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `h1`. Substitute `ht` using the available equality. Simplify using `using hst`. Establish `hspan : Submodule.span F (Set.range ![(1 : E), h]) = ⊤` using `li.span_eq_top_of_card_eq_finrank' (by simp [h2])`. Apply `hne` to reduce the goal to its premises.

Establish `hlin : σ.toLinearMap = LinearMap.id`. Apply `LinearMap.ext_on_range hspan` to reduce the goal to its premises. Introduce `i`. Use `fin_cases i`. Simplify using the standard rewrite rules.

Simplify using `using hh`. Use extensionality with `y`. Conclude with `congrArg (fun f : E →ₗ[F] E => f y) hlin`.
-/
theorem exists_algebraMap_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {σ : E →ₐ[F] E} (hne : σ ≠ AlgHom.id F E) {h : E}
    (hh : σ h = h) : ∃ c : F, h = algebraMap F E c := by
  by_contra hcon
  push Not at hcon
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), h] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hcon (-(s / t))
      have h1 : algebraMap F E t * h = -algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination h1
    subst ht
    simpa using hst
  have hspan : Submodule.span F (Set.range ![(1 : E), h]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h2])
  apply hne
  have hlin : σ.toLinearMap = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simp
    · simpa using hh
  ext y
  exact congrArg (fun f : E →ₗ[F] E => f y) hlin

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Introduce `hσ`. Use `h.2.1` as an intermediate fact. Establish `hc` using `IsTotallyComplex.complexEmbedding_not_isReal τ`. Apply `hc` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Use `h.2.2.2 τ x` as an intermediate fact. Rewrite `this` using `[hσ]`. Simplify using `using this.symm`.
-/
theorem sigma_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  intro hσ
  have := h.2.1
  have hc := IsTotallyComplex.complexEmbedding_not_isReal τ
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa using this.symm

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Simplify using `only [hE, hform, map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : (σ : E →+* E) (y j) = σ (y j)` using `rfl`. Establish `h2 : (σ : E →+* E) (y i) = σ (y i)` using `rfl`.

Rewrite using `[h1, h2, sigma_sigma hσ, hJ.1 i j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigma_hE_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (y : Fin M → E) :
    σ (hE σ J y y) = hE σ J y y := by
  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (σ : E →+* E) (y j) = σ (y j) := rfl
  have h2 : (σ : E →+* E) (y i) = σ (y i) := rfl
  rw [h1, h2, sigma_sigma hσ, hJ.1 i j]
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ d b`. Use `⟨ofF_bijective b, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[not_iff_not]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(ofF_bijective b).1 (h.trans (ofF_zero b).symm)`. Introduce and unpack `rfl`. Conclude with `ofF_zero b`. Introduce `B hB β x`.

Take `⟨c, hc⟩` from `exists_algebraMap_of_fixed hσ.2.2.1 (sigma_ne_id hσ) (sigma_hE_self hσ hJ (ofF b x 0))`. Establish `hco : (fun p : Fin M × Fin d => b.repr (ofF b x 0 p.1) p.2) = x`. Use function extensionality and compare the values at `p`. Conclude with `repr_ofF b x 0 p.1 p.2`. Establish `htr` using `hB (ofF b x 0)`.

Rewrite `htr` using `[hco, hc, Algebra.trace_algebraMap, hσ.2.2.1]`. Establish `hgram : gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ c = β`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0` using `congrFun (congrFun h 0) 0`.

Establish `h1 : hE σ J (ofF b x 0) (ofF b x 0) = algebraMap F E β` using `h0`. Rewrite `h1` using `[hc]`. Conclude with `(algebraMap F E).injective h1`. Introduce and unpack `rfl`. Use function extensionality and compare the values at `u v`.

Take `rfl : u = 0` from `Subsingleton.elim _ _`. Take `rfl : v = 0` from `Subsingleton.elim _ _`. Conclude with `hc`. Rewrite using `[hgram, ← htr, nsmul_eq_mul]`. Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`.

Establish `e : (1 / 2 : F) * (((2 : ℕ) : F) * c) = c`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.
-/
theorem ofF_gram_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧
    (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧
    ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F),
      (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) =
        (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ
          (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) →
      ∀ (β : F) (x : Fin M × Fin d → F),
        gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔
          (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  refine ⟨ofF_bijective b, ?_, ?_⟩
  · intro x
    rw [not_iff_not]
    constructor
    · intro h
      exact (ofF_bijective b).1 (h.trans (ofF_zero b).symm)
    · rintro rfl
      exact ofF_zero b
  · intro B hB β x
    obtain ⟨c, hc⟩ := exists_algebraMap_of_fixed hσ.2.2.1 (sigma_ne_id hσ)
      (sigma_hE_self hσ hJ (ofF b x 0))
    have hco : (fun p : Fin M × Fin d => b.repr (ofF b x 0 p.1) p.2) = x := by
      funext p
      exact repr_ofF b x 0 p.1 p.2
    have htr := hB (ofF b x 0)
    rw [hco, hc, Algebra.trace_algebraMap, hσ.2.2.1] at htr
    have hgram : gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ c = β := by
      constructor
      · intro h
        have h0 := congrFun (congrFun h 0) 0
        have h1 : hE σ J (ofF b x 0) (ofF b x 0) = algebraMap F E β := h0
        rw [hc] at h1
        exact (algebraMap F E).injective h1
      · rintro rfl
        funext u v
        obtain rfl : u = 0 := Subsingleton.elim _ _
        obtain rfl : v = 0 := Subsingleton.elim _ _
        exact hc
    rw [hgram, ← htr, nsmul_eq_mul]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e : (1 / 2 : F) * (((2 : ℕ) : F) * c) = c := by
      push_cast
      field_simp
    rw [e]

end GlobalTheory.CompanionTheory.SW.BB.RatCoord
