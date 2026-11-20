import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

/- English proof (translation)
Establish `hv` using `(Finset.mem_filter.1 h).2`. Use `Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩` and prove the remaining obligations. Establish `hI` using `(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) v)`. Establish `e : τ ((RingOfIntegers.mapRingEquiv (GlobalTheory.SplitPts.conjE E) x : 𝓞 E) : E) = ComplexEmbedding.conjugate τ (x : E)`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Conclude with `IsCMField.complexEmbedding_complexConj E τ x`. Rewrite using `[hI, Ideal.mem_comap]`. Use `(hv _).trans ?_` and prove the remaining obligations. Rewrite using `[e]`.
-/
private theorem conj_mem_Ov {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (h : τ ∈ UpperTheory.V.Z.Int.Ov ι v) :
    ComplexEmbedding.conjugate τ ∈ UpperTheory.V.Z.Int.Ov ι (conjSrc (GlobalTheory.SplitPts.conjE E) v) := by
  have hv := (Finset.mem_filter.1 h).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩
  have hI := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) v)
  have e : τ ((RingOfIntegers.mapRingEquiv (GlobalTheory.SplitPts.conjE E) x : 𝓞 E) : E) =
      ComplexEmbedding.conjugate τ (x : E) := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact IsCMField.complexEmbedding_complexConj E τ x
  rw [hI, Ideal.mem_comap]
  refine (hv _).trans ?_
  rw [e]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (Ideal.ext fun x => ((Finset.mem_filter.1 h₁).2 x).trans ((Finset.mem_filter.1 h₂).2 x).symm)`.
-/
private theorem eq_of_mem_Ov {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]
    {u v : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (h₁ : τ ∈ UpperTheory.V.Z.Int.Ov ι u) (h₂ : τ ∈ UpperTheory.V.Z.Int.Ov ι v) :
    u = v :=
  HeightOneSpectrum.ext (Ideal.ext fun x =>
    ((Finset.mem_filter.1 h₁).2 x).trans ((Finset.mem_filter.1 h₂).2 x).symm)

/- English proof (translation)
Introduce `l _ ι E _ _ _ w hw τ`. Take `⟨hne, -, hover⟩` from `GlobalTheory.SplitPts.over_split hw`. Use `⟨fun h hc => hne (eq_of_mem_Ov ι (conj_mem_Ov ι h) hc), fun u hu huw hunder => ?_⟩` and prove the remaining obligations. Establish `hcu : u = conjSrc (GlobalTheory.SplitPts.conjE E) w` using `(hover u hunder).resolve_left huw`. Establish `h` using `conj_mem_Ov ι hu`.

Rewrite `h` using `[hcu, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.Int.placeConj :
    UpperTheory.V.Z.Int.PlaceConj := by
  intro l _ ι E _ _ _ w hw τ
  obtain ⟨hne, -, hover⟩ := GlobalTheory.SplitPts.over_split hw
  refine ⟨fun h hc => hne (eq_of_mem_Ov ι (conj_mem_Ov ι h) hc), fun u hu huw hunder => ?_⟩
  have hcu : u = conjSrc (GlobalTheory.SplitPts.conjE E) w := (hover u hunder).resolve_left huw
  have h := conj_mem_Ov ι hu
  rwa [hcu, GlobalTheory.SplitPts.conjSrc_conjSrc_cm] at h
