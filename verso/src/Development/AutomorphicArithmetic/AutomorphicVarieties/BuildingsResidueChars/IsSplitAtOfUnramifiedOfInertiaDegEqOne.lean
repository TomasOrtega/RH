import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

/- English proof (translation)
Introduce `E _ _ _ w hun hf`. Use `set F := maximalRealSubfield E`. Use `set P : Ideal (𝓞 E) := w.asIdeal`. Use `set p : Ideal (𝓞 F) := P.under (𝓞 F)`. Establish `hfin : Module.finrank (𝓞 F) (𝓞 E) = 2`.

Rewrite using `[← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]`. Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two F E`. Establish `he : P.ramificationIdx (𝓞 F) = 1` using `Ideal.ramificationIdx_eq_one P (𝓞 F)`. Establish `hf' : P.inertiaDeg (𝓞 F) = 1`. Establish `h` using `Ideal.inertiaDeg_tower (R := ℤ) p P`.

Rewrite `h` using `[hf]`. Conclude with `(Nat.eq_one_of_mul_eq_one_left h.symm)`. Assume the negation of the conclusion as `hns`. Establish `hone : ∀ q : p.primesOver (𝓞 E), q.1 = P`. Introduce `q`.

Assume the negation of the conclusion as `hq`. Apply `hns` to reduce the goal to its premises. Establish `hq0 : q.1 ≠ ⊥`. Introduce `h0`. Establish `hP0 : p = ⊥`.

Use `q.2.2` as an intermediate fact. Rewrite `this` using `[Ideal.liesOver_iff, h0]`. Rewrite using `[this]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Apply `w.ne_bot` to reduce the goal to its premises.

Conclude with `Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) hP0`. Use `⟨⟨q.1, q.2.1, hq0⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Conclude with `hq (congrArg HeightOneSpectrum.asIdeal h)`. Use `ext1`.

Express the relevant statement in the definitionally equal form `Ideal.under (𝓞 F) q.1 = p`. Conclude with `(Ideal.liesOver_iff _ _).mp q.2.2 |>.symm`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)`. Establish `hPmem : P ∈ p.primesOver (𝓞 E)` using `⟨w.isPrime, ⟨rfl⟩⟩`. Establish `huniq : (Finset.univ : Finset (p.primesOver (𝓞 E))) = {⟨P, hPmem⟩}`.

Use extensionality with `q`. Simplify using `only [Finset.mem_univ, Finset.mem_singleton, true_iff]`. Conclude with `Subtype.ext (hone q)`. Rewrite `hsum` using `[huniq, Finset.sum_singleton, he, hf', hfin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → w.asIdeal.inertiaDeg ℤ = 1 → IsSplitAt w := by
  intro E _ _ _ w hun hf
  classical
  set F := maximalRealSubfield E
  set P : Ideal (𝓞 E) := w.asIdeal
  set p : Ideal (𝓞 F) := P.under (𝓞 F)
  have hfin : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have he : P.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one P (𝓞 F)
  have hf' : P.inertiaDeg (𝓞 F) = 1 := by
    have h := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at h
    exact (Nat.eq_one_of_mul_eq_one_left h.symm)
  by_contra hns
  have hone : ∀ q : p.primesOver (𝓞 E), q.1 = P := by
    intro q
    by_contra hq
    apply hns
    have hq0 : q.1 ≠ ⊥ := by
      intro h0
      have hP0 : p = ⊥ := by
        have := q.2.2
        rw [Ideal.liesOver_iff, h0] at this
        rw [this]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      apply w.ne_bot
      exact Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) hP0
    refine ⟨⟨q.1, q.2.1, hq0⟩, ?_, ?_⟩
    · intro h
      exact hq (congrArg HeightOneSpectrum.asIdeal h)
    · ext1
      change Ideal.under (𝓞 F) q.1 = p
      exact (Ideal.liesOver_iff _ _).mp q.2.2 |>.symm
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  have huniq : (Finset.univ : Finset (p.primesOver (𝓞 E))) = {⟨P, hPmem⟩} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hone q)
  rw [huniq, Finset.sum_singleton, he, hf', hfin] at hsum
  omega
