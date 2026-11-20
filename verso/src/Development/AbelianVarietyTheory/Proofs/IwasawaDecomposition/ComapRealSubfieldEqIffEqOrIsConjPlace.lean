import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.PlacePair

/- English proof (translation)
The claim follows from `D.host.φ₀.injective (by rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`.
-/
theorem hostConj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]`. Conclude with `IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)`.
-/
theorem cO_cO (D : D7) (x : 𝓞 D.host.E) :
    IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
  exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)

/- English proof (translation)
The claim follows from `(IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩`.
-/
theorem cO_algebraMap (D : D7) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    IsCMField.ringOfIntegersComplexConj D.host.E
        (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a) =
      algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `h x _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, hostConj_eq])`. Introduce `h x y hxy`. Establish `: y = IsCMField.ringOfIntegersComplexConj D.host.E x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hxy, hostConj_eq, IsCMField.coe_ringOfIntegersComplexConj]`. Rewrite using `[this]`. Conclude with `h x`.
-/
theorem isConjPl_iff (D : D7) (P P' : PlE D.host) :
    IsConjPl D.host P P' ↔
      ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ IsCMField.ringOfIntegersComplexConj D.host.E x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, hostConj_eq])
  · intro h x y hxy
    have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      rw [hxy, hostConj_eq, IsCMField.coe_ringOfIntegersComplexConj]
    rw [this]; exact h x

/- English proof (translation)
Use `set Q : Ideal (𝓞 D.host.E) := P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) with hQ`. Establish `hQp : Q.IsPrime` using `Ideal.comap_isPrime _ _`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨h1, h2⟩` from `hne`.

Establish `nle : ∀ I : Ideal (𝓞 D.host.E), I.IsPrime → w.asIdeal ≠ I → ¬ w.asIdeal ≤ I` using `fun I hI h hle => h (w.isMaximal.eq_of_le hI.ne_top hle)`. Take `⟨a, ha, haP⟩` from `Set.not_subset.mp (nle P.asIdeal P.isPrime h1)`. Take `⟨b, hb, hbQ⟩` from `Set.not_subset.mp (nle Q hQp h2)`. Establish `key : ∃ x ∈ w.asIdeal, x ∉ P.asIdeal ∧ x ∉ Q`. Distinguish the cases in `haQ : a ∈ Q`.

Distinguish the cases in `hbP : b ∈ P.asIdeal`. Use `⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩` and prove the remaining obligations. Simplify using `using P.asIdeal.sub_mem h hbP`. Simplify using `using Q.sub_mem h haQ`. Conclude with `⟨b, hb, hbP, hbQ⟩`.

Conclude with `⟨a, ha, haP, haQ⟩`. Take `⟨x, hx, hxP, hxQ⟩` from `key`. Establish `hxQ' : IsCMField.ringOfIntegersComplexConj D.host.E x ∉ P.asIdeal` using `hxQ`. Establish `hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) = x * IsCMField.ringOfIntegersComplexConj D.host.E x`. Rewrite using `[map_mul, cO_cO, mul_comm]`.

Take `⟨y, hy⟩` from `(IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix`. Establish `hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))`. Rewrite using `[Ideal.mem_comap, hy]`. Conclude with `w.asIdeal.mul_mem_right _ hx`. Rewrite `hyw` using `[hw, Ideal.mem_comap, hy]`.

Break down `P.isPrime.mem_or_mem hyw with h | h` into its components or cases. Conclude with `hxP h`. Conclude with `hxQ' h`.
-/
theorem eq_or_eq_conj (D : D7) (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w.asIdeal = P.asIdeal ∨
      w.asIdeal = P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  set Q : Ideal (𝓞 D.host.E) :=
    P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  by_contra hne
  push_neg at hne
  obtain ⟨h1, h2⟩ := hne
  have nle : ∀ I : Ideal (𝓞 D.host.E), I.IsPrime → w.asIdeal ≠ I → ¬ w.asIdeal ≤ I := fun I hI h hle =>
    h (w.isMaximal.eq_of_le hI.ne_top hle)
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle P.asIdeal P.isPrime h1)
  obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q hQp h2)
  have key : ∃ x ∈ w.asIdeal, x ∉ P.asIdeal ∧ x ∉ Q := by
    by_cases haQ : a ∈ Q
    · by_cases hbP : b ∈ P.asIdeal
      · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
        · simpa using P.asIdeal.sub_mem h hbP
        · simpa using Q.sub_mem h haQ
      · exact ⟨b, hb, hbP, hbQ⟩
    · exact ⟨a, ha, haP, haQ⟩
  obtain ⟨x, hx, hxP, hxQ⟩ := key
  have hxQ' : IsCMField.ringOfIntegersComplexConj D.host.E x ∉ P.asIdeal := hxQ
  have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
      x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
    rw [map_mul, cO_cO, mul_comm]
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
  have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
  rw [hw, Ideal.mem_comap, hy] at hyw
  rcases P.isPrime.mem_or_mem hyw with h | h
  · exact hxP h
  · exact hxQ' h

/- English proof (translation)
Introduce `D P P'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `eq_or_eq_conj D P P' h.symm with e | e` into its components or cases. Conclude with `Or.inl (HeightOneSpectrum.ext e.symm)`.

Use `Or.inr ((isConjPl_iff D P P').2 fun x => ?_)` and prove the remaining obligations. Rewrite using `[e, Ideal.mem_comap, RingHom.coe_coe, cO_cO]`. Introduce and unpack `(rfl | h)`. Both sides reduce to the same expression. Rewrite `h` using `[isConjPl_iff]`.

Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, h, cO_algebraMap]`.
-/
theorem comap_eq_iff : ∀ (D : D7) (P P' : PlE D.host),
    P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ↔
        (P = P' ∨ IsConjPl D.host P P') := by
  intro D P P'
  constructor
  · intro h
    rcases eq_or_eq_conj D P P' h.symm with e | e
    · exact Or.inl (HeightOneSpectrum.ext e.symm)
    · refine Or.inr ((isConjPl_iff D P P').2 fun x => ?_)
      rw [e, Ideal.mem_comap, RingHom.coe_coe, cO_cO]
  · rintro (rfl | h)
    · rfl
    · rw [isConjPl_iff] at h
      ext a
      rw [Ideal.mem_comap, Ideal.mem_comap, h, cO_algebraMap]

end GlobalTheory.PlacePair
