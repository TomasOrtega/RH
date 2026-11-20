import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelicStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FinQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, -, -, hτ⟩` from `h`. Set `w : InfinitePlace E` to `Classical.arbitrary _`. Apply `w.embedding.injective` to reduce the goal to its premises. Rewrite using `[hτ, hτ, star_star]`.
-/
theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨-, htc, -, hτ⟩` from `h`. Set `w : InfinitePlace E` to `Classical.arbitrary _`. Establish `hcx : w.IsComplex` using `htc.isComplex w`.

Apply `InfinitePlace.not_isReal_iff_isComplex.mpr hcx` to reduce the goal to its premises. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Use `hτ w.embedding x` as an intermediate fact. Rewrite `this` using `[hc x]`.

Simplify using `using this.symm`.
-/
theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨-, htc, -, hτ⟩ := h
  let w : InfinitePlace E := Classical.arbitrary _
  have hcx : w.IsComplex := htc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.mpr hcx
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  have := hτ w.embedding x
  rw [hc x] at this
  simpa using this.symm

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_moved σ h`. Establish `hd : x - σ x ≠ 0` using `fun h0 => hx (sub_eq_zero.mp h0).symm`. Establish `hli : LinearIndependent F ![(1 : E), x]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Establish `h2` using `congrArg σ hst`. Simplify using `only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, map_zero] at h2`. Establish `h3 : t • (x - σ x) = 0`. Simplify using `only [Algebra.smul_def] at hst ⊢`. Take the linear combination `hst - h2`.

Establish `ht : t = 0` using `(smul_eq_zero.mp h3).resolve_right hd`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero] at hst`. Use `⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩` and prove the remaining obligations. Establish `hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤` using `hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])`.

Establish `hmem : e ∈ Submodule.span F ({(1 : E), x} : Set E)`. Establish `: e ∈ Submodule.span F (Set.range ![(1 : E), x])` using `by rw [hspan]; trivial`. Simplify `this` using `[Matrix.range_cons, Matrix.range_empty, Set.pair_comm]`. Take `⟨a, b, hab⟩` from `Submodule.mem_span_pair.mp hmem`. Establish `h2 : a • (1 : E) + b • σ x = e`.

Use `congrArg σ hab` as an intermediate fact. Simplify using `only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, he] at this`. Simplify `this` using `only [Algebra.smul_def]`. Establish `h3 : b • (x - σ x) = 0`. Simplify using `only [Algebra.smul_def] at hab h2 ⊢`.

Take the linear combination `hab - h2`. Establish `hb : b = 0` using `(smul_eq_zero.mp h3).resolve_right hd`. Substitute `hb` using the available equality. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hab, Algebra.algebraMap_eq_smul_one]`.

Simplify using the standard rewrite rules.
-/
theorem fixed_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ t : F, e = algebraMap F E t := by
  obtain ⟨x, hx⟩ := exists_moved σ h
  have hd : x - σ x ≠ 0 := fun h0 => hx (sub_eq_zero.mp h0).symm
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, map_zero] at h2
    have h3 : t • (x - σ x) = 0 := by
      simp only [Algebra.smul_def] at hst ⊢
      linear_combination hst - h2
    have ht : t = 0 := (smul_eq_zero.mp h3).resolve_right hd
    subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])
  have hmem : e ∈ Submodule.span F ({(1 : E), x} : Set E) := by
    have : e ∈ Submodule.span F (Set.range ![(1 : E), x]) := by rw [hspan]; trivial
    simpa [Matrix.range_cons, Matrix.range_empty, Set.pair_comm] using this
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  have h2 : a • (1 : E) + b • σ x = e := by
    have := congrArg σ hab
    simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, he] at this
    simpa only [Algebra.smul_def] using this
  have h3 : b • (x - σ x) = 0 := by
    simp only [Algebra.smul_def] at hab h2 ⊢
    linear_combination hab - h2
  have hb : b = 0 := (smul_eq_zero.mp h3).resolve_right hd
  subst hb
  refine ⟨a, ?_⟩
  rw [← hab, Algebra.algebraMap_eq_smul_one]
  simp

/- English proof (translation)
Simplify using `only [hE, hform, map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : σ ((σ : E →+* E) (x j)) = x j` using `sigma_sigma σ h (x j)`. Establish `h2 : σ (J j i) = J i j` using `hJ.1 i j`.

Establish `h3 : (σ : E →+* E) (x i) = σ (x i)` using `rfl`. Rewrite using `[h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_self_fixed (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma σ h (x j)
  have h2 : σ (J j i) = J i j := hJ.1 i j
  have h3 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, h2, h3]
  ring

end Field

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X`. Take `⟨t, ht⟩` from `fixed_mem σ hcm _ (hE_self_fixed σ hcm J hJ (X 0))`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a b`. Rewrite using `[Subsingleton.elim a 0, Subsingleton.elim b 0]`. Conclude with `ht`. Introduce `n X`. Use extensionality with `a b`.

Establish `hs : ∀ e : E, sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e)` using `fun e => by`. Simplify using `[sigR, inclR]`. Simplify using `only [gramR, hR, hform, ratTup, JR, Matrix.map_apply, gramE, hE, map_sum, map_mul, hs]`. Both sides reduce to the same expression. Introduce `Ω hΩ`.

Take `⟨⟨hlc, hsc, ht2⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Establish `hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _)` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J`. Set `φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E` to `fun Y _ _ => gramR (AF F) σ J Y 0 0`. Establish `hφ : Continuous φ` using `continuous_pi fun _ => continuous_pi fun _ => hcont.matrix_elem 0 0`. Establish `hfin` using `(GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hcm 1 1).2.1 _ (hΩ.image hφ)`.

Set `ι : F → Fin 1 → Fin 1 → E` to `fun t _ _ => algebraMap F E t`. Use `Set.Finite.of_injOn (f := ι) ?_ ?_ hfin` and prove the remaining obligations. Introduce and unpack `t ⟨Y, hY, hYt⟩`. Use `⟨Y, hY, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a b`.

Conclude with `congrFun (congrFun hYt 0) 0`. Introduce `s _ t _ hst`. Conclude with `(algebraMap F E).injective (congrFun (congrFun hst 0) 0)`.
-/
theorem gram_rational_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X : Fin 1 → Fin M → E, ∃ t : F, gramE σ J X = fun _ _ => algebraMap F E t) ∧
    (∀ (n : ℕ) (X : Fin n → Fin M → E),
      gramR (AF F) σ J (ratTup (AF F) X) = (gramE σ J X).map (inclR (AF F))) ∧
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      {t : F | ∃ Y ∈ Ω, gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)}.Finite := by
  intro F E _ _ _ _ _ σ hcm M J hJ
  refine ⟨?_, ?_, ?_⟩
  · intro X
    obtain ⟨t, ht⟩ := fixed_mem σ hcm _ (hE_self_fixed σ hcm J hJ (X 0))
    refine ⟨t, ?_⟩
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact ht
  · intro n X
    ext a b
    have hs : ∀ e : E, sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := fun e => by
      simp [sigR, inclR]
    simp only [gramR, hR, hform, ratTup, JR, Matrix.map_apply, gramE, hE, map_sum, map_mul, hs]
    rfl
  · intro Ω hΩ
    obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
    let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
      fun Y _ _ => gramR (AF F) σ J Y 0 0
    have hφ : Continuous φ :=
      continuous_pi fun _ => continuous_pi fun _ => hcont.matrix_elem 0 0
    have hfin := (GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hcm 1 1).2.1 _ (hΩ.image hφ)
    let ι : F → Fin 1 → Fin 1 → E := fun t _ _ => algebraMap F E t
    refine Set.Finite.of_injOn (f := ι) ?_ ?_ hfin
    · rintro t ⟨Y, hY, hYt⟩
      refine ⟨Y, hY, ?_⟩
      funext a b
      exact congrFun (congrFun hYt 0) 0
    · intro s _ t _ hst
      exact (algebraMap F E).injective (congrFun (congrFun hst 0) 0)

end GlobalTheory.CompanionTheory.SW.FinQ
