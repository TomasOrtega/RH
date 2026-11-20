import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap

open IsDedekindDomain NumberField

namespace GlobalTheory.FixedPrime

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `y hy`. Take `⟨s, hs⟩` from `(IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by`. Rewrite using `[map_mul, mul_comm]`. Use `congr 1`. Use `ext`.

Use the proof step `simp)`. Establish `h1 : s ∈ Q.under (𝓞 (maximalRealSubfield E))`. Rewrite using `[Ideal.under_def, Ideal.mem_comap, hs]`. Conclude with `Q.mul_mem_right _ hy`. Establish `h2` using `hQ h1`.

Rewrite `h2` using `[Ideal.under_def, Ideal.mem_comap, hs]`. Conclude with `(hP.mem_or_mem h2).elim id (h y)`.
-/
theorem le_of_under_le (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P → x ∈ P) (Q : Ideal (𝓞 E))
    (hQ : Q.under (𝓞 (maximalRealSubfield E)) ≤ P.under (𝓞 (maximalRealSubfield E))) : Q ≤ P := by
  intro y hy
  obtain ⟨s, hs⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by
      rw [map_mul, mul_comm]
      congr 1
      ext; simp)
  have h1 : s ∈ Q.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under_def, Ideal.mem_comap, hs]
    exact Q.mul_mem_right _ hy
  have h2 := hQ h1
  rw [Ideal.under_def, Ideal.mem_comap, hs] at h2
  exact (hP.mem_or_mem h2).elim id (h y)

/- English proof (translation)
Use `haveI := P.isPrime`. Use `haveI : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal := Algebra.unramified_iff_forall.1 inferInstance ⟨P.asIdeal, P.isPrime⟩`. Use `set v := P.under (𝓞 (maximalRealSubfield E)) with hv`. Establish `hva : v.asIdeal = P.asIdeal.under (𝓞 (maximalRealSubfield E))` using `rfl`. Establish `hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))` using `FaithfulSMul.algebraMap_injective _ _`.

Unfold `Formalism.UG.IsInertAt`. Rewrite using `[hva]`. Establish `hle : (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal` using `Ideal.map_comap_le`. Establish `h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal = 1`. Use `letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal`.

Conclude with `(Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2 ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E)) (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal).1 ‹_›).2`. Establish `h2 : ¬ (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal ^ 2` using `fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1`. Use `set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) (P.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI`. Establish `hI0 : I ≠ ⊥`. Rewrite using `[hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]`.

Conclude with `v.ne_bot`. Establish `hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = P.asIdeal`. Introduce `p hp`. Take `⟨hpp, hpl⟩` from `(Ideal.mem_normalizedFactors_iff hI0).1 hp`. Establish `hp0 : p ≠ ⊥` using `fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))`.

Use `(hpp.isMaximal hp0).eq_of_le P.isPrime.ne_top (le_of_under_le P.asIdeal h p ?_)` and prove the remaining obligations. Conclude with `(v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top) (Ideal.map_le_iff_le_comap.1 hpl)).ge`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, I = P.asIdeal ^ n := by`. Use `⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]`.

Rewrite using `[Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]`. Break down `n with _ | _ | n` into its components or cases. It suffices to derive a contradiction. Rewrite `hle` using `[hn, pow_zero, Ideal.one_eq_top, top_le_iff]`. Conclude with `P.isPrime.ne_top hle`.

Simplify using `using hn`. Conclude with `absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2`.
-/
theorem isInertAt_under [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal → x ∈ P.asIdeal) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (P.under (𝓞 (maximalRealSubfield E))) P := by
  classical
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal :=
    Algebra.unramified_iff_forall.1 inferInstance ⟨P.asIdeal, P.isPrime⟩
  set v := P.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = P.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (P.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = P.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    refine (hpp.isMaximal hp0).eq_of_le P.isPrime.ne_top (le_of_under_le P.asIdeal h p ?_)
    exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
      (Ideal.map_le_iff_le_comap.1 hpl)).ge
  obtain ⟨n, hn⟩ : ∃ n, I = P.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact P.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

/- English proof (translation)
Take `⟨σ, ϖ, h1, h2, h3, h4, h5, h6⟩` from `GlobalTheory.InertConj.exists_conj_completion E v P h`. Use `⟨σ, ϖ, h1, h2, h3, h5, h6, h4, ?_, ?_⟩` and prove the remaining obligations. Establish `a : Ideal.absNorm v.asIdeal ≠ 1` using `fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)`. Establish `b : Ideal.absNorm v.asIdeal ≠ 0` using `fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Use linear arithmetic over natural numbers and integers.

Establish `hN : Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ 2`. Rewrite using `[← show Ideal.map _ v.asIdeal = P.asIdeal from h, Ideal.absNorm_algebraMap, ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]`. Use `congr 1`. Conclude with `(Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E).symm`. Rewrite using `[← hN]`.

Conclude with `Formalism.UG.P.tjcosets_card_residue P`.
-/
theorem exists_isUnramInv [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E v P) :
    ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E),
      (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
        algebraMap E (P.adicCompletion E) (IsCMField.complexConj E x)) ∧
      Formalism.UG.IsUnramInv ϖ σ (Ideal.absNorm v.asIdeal) := by
  obtain ⟨σ, ϖ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.InertConj.exists_conj_completion E v P h
  refine ⟨σ, ϖ, h1, h2, h3, h5, h6, h4, ?_, ?_⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← show Ideal.map _ v.asIdeal = P.asIdeal from h, Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue P

end CM

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D P hP`. Use `haveI := D.host.isCMField_hostE`. Use `haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm`. Establish `h` using `isInertAt_under P fun x hx => by`. Rewrite using `[← hP, Formalism.L2.Col.mem_conjIdeal]`.

Conclude with `hx`. Take `⟨σ, ϖ, h1, h2⟩` from `exists_isUnramInv _ P h`. Conclude with `⟨σ, ϖ, _, h1, h2⟩`.
-/
theorem exists_isConjAt_isUnramInv : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal → ∃ (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (ϖ : P.adicCompletion D.host.E) (q : ℕ), IsConjAt P σ ∧ Formalism.UG.IsUnramInv ϖ σ q := by
  intro D P hP
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  have h := isInertAt_under P fun x hx => by
    rw [← hP, Formalism.L2.Col.mem_conjIdeal]
    exact hx
  obtain ⟨σ, ϖ, h1, h2⟩ := exists_isUnramInv _ P h
  exact ⟨σ, ϖ, _, h1, h2⟩

end GlobalTheory.FixedPrime
