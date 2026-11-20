import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Take `⟨ι, B, hB⟩` from `exists_isTranscendenceBasis' (algebraicClosure F E) E`. Set `` to `IsAlgClosed.isAlgClosure_of_transcendence_basis B hB`. Set `e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E] Algebra.adjoin (algebraicClosure F E) (Set.range B)` to `hB.1.aevalEquiv`. Set `m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E)` to `MvPolynomial.mapEquiv ι σ₀.toRingEquiv`. Set `e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+* Algebra.adjoin (algebraicClosure F E) (Set.range B)` to `e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)`.

Set `σ : E ≃+* E` to `IsAlgClosure.equivOfEquiv E E e`. Establish `he : ∀ a : algebraicClosure F E, e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a)`. Introduce `a`. Simplify using `only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]`. Rewrite using `[MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]`.

Both sides reduce to the same expression. Establish `hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E)`. Introduce `a`. Establish `h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E (algebraMap _ _ a)` using `rfl`. Rewrite using `[h1, IsAlgClosure.equivOfEquiv_algebraMap, he]`.

Both sides reduce to the same expression. Use `⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩` and prove the remaining obligations. Introduce `r`. Establish `h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E)`. Both sides reduce to the same expression.

Rewrite using `[h1, hσ, AlgEquiv.commutes]`.
-/
theorem exists_algEquiv_extending {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
  obtain ⟨ι, B, hB⟩ := exists_isTranscendenceBasis' (algebraicClosure F E) E
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis B hB
  let e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E]
      Algebra.adjoin (algebraicClosure F E) (Set.range B) := hB.1.aevalEquiv
  let m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E) :=
    MvPolynomial.mapEquiv ι σ₀.toRingEquiv
  let e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+*
      Algebra.adjoin (algebraicClosure F E) (Set.range B) :=
    e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)
  let σ : E ≃+* E := IsAlgClosure.equivOfEquiv E E e
  have he : ∀ a : algebraicClosure F E,
      e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a) := by
    intro a
    simp only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
    intro a
    have h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E
        (algebraMap _ _ a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩
  intro r
  have h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E) :=
    rfl
  rw [h1, hσ, AlgEquiv.commutes]

/- English proof (translation)
Introduce `F z hz hfix`. Establish `hzF : IsAlgebraic F z` using `hz.tower_top F`. Establish `hzA : z ∈ algebraicClosure F ℂ` using `(mem_algebraicClosure_iff).2 hzF`. Establish `: IsGalois F (algebraicClosure F ℂ)` using `inferInstance`. Take `⟨r, hr⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) (K := algebraicClosure F ℂ) ⟨z, hzA⟩).2 (by`.

Introduce `σ₀`. Take `⟨σ, hσ⟩` from `exists_algEquiv_extending σ₀`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hσ]`. Conclude with `hfix σ)`.

Establish `: (r : ℂ) = z` using `congrArg Subtype.val hr`. Rewrite using `[← this]`. Conclude with `r.2`.
-/
theorem fixed_by_automorphism_in_field : FixedByAutInField := by
  intro F z hz hfix
  have hzF : IsAlgebraic F z := hz.tower_top F
  have hzA : z ∈ algebraicClosure F ℂ := (mem_algebraicClosure_iff).2 hzF
  have : IsGalois F (algebraicClosure F ℂ) := inferInstance
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (k := F) (K := algebraicClosure F ℂ) ⟨z, hzA⟩).2 (by
      intro σ₀
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending σ₀
      apply Subtype.ext
      rw [← hσ]
      exact hfix σ)
  have : (r : ℂ) = z := congrArg Subtype.val hr
  rw [← this]
  exact r.2

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
