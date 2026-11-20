import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LocalFinite

/- English proof (translation)
Introduce `O R _ _ _ _ _`. Use `haveI : Algebra.IsIntegral O R := Algebra.IsIntegral.of_finite O R`. Use `set m := IsLocalRing.maximalIdeal O with hm`. Use `set I : Ideal R := Ideal.map (algebraMap O R) m with hI`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `M ⟨-, hM⟩`. Use `Ideal.map_le_iff_le_comap.mpr ?_` and prove the remaining obligations. Use `haveI : (Ideal.comap (algebraMap O R) M).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Conclude with `(IsLocalRing.eq_maximalIdeal this).ge`.

Establish `hle : m ≤ Ideal.comap (algebraMap O R) I` using `Ideal.le_comap_map`. Set `f : (O ⧸ m) →+* (R ⧸ I)` to `Ideal.quotientMap I (algebraMap O R) hle`. Use `letI : Field (O ⧸ m) := Ideal.Quotient.field m`. Use `letI : Algebra (O ⧸ m) (R ⧸ I) := f.toAlgebra`. Establish `hcomp : (f.comp (Ideal.Quotient.mk m)).Finite`.

Establish `h1 : (algebraMap O R).Finite` using `RingHom.finite_algebraMap.mpr inferInstance`. Establish `h2 : (Ideal.Quotient.mk I).Finite` using `RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h3 : f.comp (Ideal.Quotient.mk m) = (Ideal.Quotient.mk I).comp (algebraMap O R)`. Use extensionality with `x`. Simplify using `[f]`.

Rewrite using `[h3]`. Conclude with `h2.comp h1`. Establish `hf : f.Finite` using `RingHom.Finite.of_comp_finite hcomp`. Use `haveI : Module.Finite (O ⧸ m) (R ⧸ I) := hf`. Use `haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (O ⧸ m) (R ⧸ I)`.

Take `⟨N, hN⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `hmap : Ideal.map (Ideal.Quotient.mk I) (⊥ : Ideal R).jacobson ≤ (⊥ : Ideal (R ⧸ I)).jacobson`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `P ⟨-, hP⟩`.

Use `Ideal.map_le_iff_le_comap.mpr ?_` and prove the remaining obligations. Use `haveI : (Ideal.comap (Ideal.Quotient.mk I) P).IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Conclude with `sInf_le ⟨bot_le, this⟩`. Establish `hz : Ideal.map (Ideal.Quotient.mk I) ((⊥ : Ideal R).jacobson ^ N) = ⊥`. Rewrite using `[Ideal.map_pow]`.

Conclude with `le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans hN.le)`. Introduce `x hx`. Establish `: Ideal.Quotient.mk I x = 0`. Use `Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx` as an intermediate fact. Rewrite `this` using `[hz]`.

Simplify using `using this`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp this`.
-/
theorem map_maximalIdeal_le_jacobson_and_pow_le :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R],
      Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧
        ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤
          Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  intro O R _ _ _ _ _
  haveI : Algebra.IsIntegral O R := Algebra.IsIntegral.of_finite O R
  set m := IsLocalRing.maximalIdeal O with hm
  set I : Ideal R := Ideal.map (algebraMap O R) m with hI
  refine ⟨?_, ?_⟩
  · refine le_sInf ?_
    rintro M ⟨-, hM⟩
    refine Ideal.map_le_iff_le_comap.mpr ?_
    haveI : (Ideal.comap (algebraMap O R) M).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  · have hle : m ≤ Ideal.comap (algebraMap O R) I := Ideal.le_comap_map
    let f : (O ⧸ m) →+* (R ⧸ I) := Ideal.quotientMap I (algebraMap O R) hle
    letI : Field (O ⧸ m) := Ideal.Quotient.field m
    letI : Algebra (O ⧸ m) (R ⧸ I) := f.toAlgebra
    have hcomp : (f.comp (Ideal.Quotient.mk m)).Finite := by
      have h1 : (algebraMap O R).Finite := RingHom.finite_algebraMap.mpr inferInstance
      have h2 : (Ideal.Quotient.mk I).Finite :=
        RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
      have h3 : f.comp (Ideal.Quotient.mk m) = (Ideal.Quotient.mk I).comp (algebraMap O R) := by
        ext x; simp [f]
      rw [h3]
      exact h2.comp h1
    have hf : f.Finite := RingHom.Finite.of_comp_finite hcomp
    haveI : Module.Finite (O ⧸ m) (R ⧸ I) := hf
    haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (O ⧸ m) (R ⧸ I)
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
    refine ⟨N, ?_⟩
    have hmap : Ideal.map (Ideal.Quotient.mk I) (⊥ : Ideal R).jacobson ≤
        (⊥ : Ideal (R ⧸ I)).jacobson := by
      refine le_sInf ?_
      rintro P ⟨-, hP⟩
      refine Ideal.map_le_iff_le_comap.mpr ?_
      haveI : (Ideal.comap (Ideal.Quotient.mk I) P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact sInf_le ⟨bot_le, this⟩
    have hz : Ideal.map (Ideal.Quotient.mk I) ((⊥ : Ideal R).jacobson ^ N) = ⊥ := by
      rw [Ideal.map_pow]
      exact le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans hN.le)
    intro x hx
    have : Ideal.Quotient.mk I x = 0 := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx
      rw [hz] at this
      simpa using this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory.CompanionTheory.LocalFinite
