import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RayFieldNorm

/- English proof (translation)
Establish `h1 : Fintype.card (InfinitePlace K) = 1`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K`. Establish `h3` using `InfinitePlace.card_add_two_mul_card_eq_rank K`. Establish `h4` using `IsTotallyComplex.nrRealPlaces_eq_zero K`. Use linear arithmetic over natural numbers and integers.

Establish `: Subsingleton (InfinitePlace K)` using `Fintype.card_le_one_iff_subsingleton.mp h1.le`. Establish `h5` using `InfinitePlace.prod_eq_abs_norm (π : K)`. Rewrite `h5` using `[Fintype.prod_subsingleton _ (InfinitePlace.mk φ), IsTotallyComplex.mult_eq, InfinitePlace.apply]`. Rewrite using `[h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]`. Simplify using the standard rewrite rules.
-/
theorem normSq_eq_absNorm {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (π : 𝓞 K) :
    ‖φ π‖ ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℝ) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

/- English proof (translation)
Rewrite using `[isTotallyComplex_iff]`. Introduce `w`. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex]`. Introduce `hw`. Take `⟨φ, hφ, -⟩` from `hw`.

Conclude with `h.elim (NumberField.ComplexEmbedding.IsReal.embedding hφ)`.
-/
theorem isTotallyComplex_of_isEmpty {K : Type} [Field K] [NumberField K]
    (h : IsEmpty (K →+* ℝ)) : IsTotallyComplex K := by
  rw [isTotallyComplex_iff]
  intro w
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  obtain ⟨φ, hφ, -⟩ := hw
  exact h.elim (NumberField.ComplexEmbedding.IsReal.embedding hφ)

/- English proof (translation)
Introduce `K _ _ hE hK j π p hp`. Use `haveI := isTotallyComplex_of_isEmpty hE`. Use `haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ`. Set `ι : Qb →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := Qb)).toRingHom`. Use `⟨(Formalism.L2.DIV.conjQb ι).toAlgHom, ?_⟩` and prove the remaining obligations.

Apply `ι.injective` to reduce the goal to its premises. Establish `hn` using `normSq_eq_absNorm hK (ι.comp j) π`. Rewrite `hn` using `[hp]`. Establish `hc : ι (j (π : K)) * starRingEnd ℂ (ι (j (π : K))) = ((‖ι (j (π : K))‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Establish `hs` using `Formalism.L2.DIV.conjQb_spec ι (j (π : K))`. Express the relevant statement in the definitionally equal form `ι (j (π : K) * (Formalism.L2.DIV.conjQb ι) (j (π : K))) = ι (p : Qb)`. Rewrite using `[map_mul, hs, hc, map_natCast]`. Simplify using `only [RingHom.comp_apply] at hn`. Rewrite using `[hn]`.

Simplify using the standard rewrite rules.
-/
theorem exists_mul_conj_eq_norm : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  intro K _ _ hE hK j π p hp
  haveI := isTotallyComplex_of_isEmpty hE
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qb →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := Qb)).toRingHom
  refine ⟨(Formalism.L2.DIV.conjQb ι).toAlgHom, ?_⟩
  apply ι.injective
  have hn := normSq_eq_absNorm hK (ι.comp j) π
  rw [hp] at hn
  have hc : ι (j (π : K)) * starRingEnd ℂ (ι (j (π : K))) = ((‖ι (j (π : K))‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs := Formalism.L2.DIV.conjQb_spec ι (j (π : K))
  change ι (j (π : K) * (Formalism.L2.DIV.conjQb ι) (j (π : K))) = ι (p : Qb)
  rw [map_mul, hs, hc, map_natCast]
  simp only [RingHom.comp_apply] at hn
  rw [hn]
  simp

end GlobalTheory.RayFieldNorm
