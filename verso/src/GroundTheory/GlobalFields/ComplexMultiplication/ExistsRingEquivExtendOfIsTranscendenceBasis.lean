import Mathlib

namespace GroundTheory.Global

open Cardinal Polynomial IntermediateField

section General

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

/- English proof (translation)
Use `IsAlgClosed.isAlgClosure_of_transcendence_basis v₁ h₁` as an intermediate fact. Use `IsAlgClosed.isAlgClosure_of_transcendence_basis v₂ h₂` as an intermediate fact. Set `e' : Algebra.adjoin F₁ (Set.range v₁) ≃+* Algebra.adjoin F₂ (Set.range v₂)` to `h₁.1.aevalEquiv.symm.toRingEquiv.trans <| (MvPolynomial.mapEquiv ι e).trans <| (MvPolynomial.renameEquiv F₂ φ).toRingEquiv.trans h₂.1.aevalEquiv.toRingEquiv`. Establish `key : ∀ p : MvPolynomial ι F₁, IsAlgClosure.equivOfEquiv Ω Ω e' (MvPolynomial.aeval v₁ p) = MvPolynomial.aeval v₂ (MvPolynomial.rename φ (MvPolynomial.map (e : F₁ →+* F₂) p))`. Introduce `p`.

Rewrite using `[← h₁.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap, ← h₂.1.algebraMap_aevalEquiv]`. Use `congr 1`. Simplify using `[e']`. Use `⟨IsAlgClosure.equivOfEquiv Ω Ω e', fun a => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `using key (MvPolynomial.C a)`.

Simplify using `using key (MvPolynomial.X i)`.
-/
theorem exists_ringEquiv_extend_of_isTranscendenceBasis
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) {ι κ : Type*} {v₁ : ι → Ω} {v₂ : κ → Ω}
    (h₁ : IsTranscendenceBasis F₁ v₁) (h₂ : IsTranscendenceBasis F₂ v₂) (φ : ι ≃ κ) :
    ∃ σ : Ω ≃+* Ω, (∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a)) ∧
      ∀ i, σ (v₁ i) = v₂ (φ i) := by
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₁ h₁
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₂ h₂
  let e' : Algebra.adjoin F₁ (Set.range v₁) ≃+* Algebra.adjoin F₂ (Set.range v₂) :=
    h₁.1.aevalEquiv.symm.toRingEquiv.trans <| (MvPolynomial.mapEquiv ι e).trans <|
      (MvPolynomial.renameEquiv F₂ φ).toRingEquiv.trans h₂.1.aevalEquiv.toRingEquiv
  have key : ∀ p : MvPolynomial ι F₁,
      IsAlgClosure.equivOfEquiv Ω Ω e' (MvPolynomial.aeval v₁ p) =
        MvPolynomial.aeval v₂ (MvPolynomial.rename φ (MvPolynomial.map (e : F₁ →+* F₂) p)) := by
    intro p
    rw [← h₁.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap,
      ← h₂.1.algebraMap_aevalEquiv]
    congr 1
    simp [e']
  refine ⟨IsAlgClosure.equivOfEquiv Ω Ω e', fun a => ?_, fun i => ?_⟩
  · simpa using key (MvPolynomial.C a)
  · simpa using key (MvPolynomial.X i)

/- English proof (translation)
Take `⟨s₁, hs₁⟩` from `exists_isTranscendenceBasis F₁ Ω`. Take `⟨s₂, hs₂⟩` from `exists_isTranscendenceBasis F₂ Ω`. Take `⟨φ⟩` from `Cardinal.eq.1 (hs₁.cardinalMk_eq_trdeg.trans (h.trans hs₂.cardinalMk_eq_trdeg.symm))`. Take `⟨σ, hσ, -⟩` from `exists_ringEquiv_extend_of_isTranscendenceBasis e hs₁ hs₂ φ`. Conclude with `⟨σ, hσ⟩`.
-/
theorem exists_ringEquiv_extend_of_trdeg_eq
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) (h : Algebra.trdeg F₁ Ω = Algebra.trdeg F₂ Ω) :
    ∃ σ : Ω ≃+* Ω, ∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a) := by
  obtain ⟨s₁, hs₁⟩ := exists_isTranscendenceBasis F₁ Ω
  obtain ⟨s₂, hs₂⟩ := exists_isTranscendenceBasis F₂ Ω
  obtain ⟨φ⟩ := Cardinal.eq.1 (hs₁.cardinalMk_eq_trdeg.trans (h.trans hs₂.cardinalMk_eq_trdeg.symm))
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis e hs₁ hs₂ φ
  exact ⟨σ, hσ⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_isTranscendenceBasis F Ω`. Rewrite using `[← hs.cardinalMk_eq_trdeg]`. Simplify using `using (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs Cardinal.mk_le_aleph0 hΩ).symm`.
-/
theorem trdeg_eq_cardinalMk_of_countable (F : Type*) [Field F] [Algebra F Ω] [Countable F]
    (hΩ : ℵ₀ < #Ω) : Algebra.trdeg F Ω = #Ω := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  rw [← hs.cardinalMk_eq_trdeg]
  simpa using (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs
    Cardinal.mk_le_aleph0 hΩ).symm

end General

/- English proof (translation)
The claim follows from `GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq e h`.
-/
theorem Complex.exists_ringEquiv_extend_of_trdeg_eq (F₁ F₂ : Subfield ℂ) (e : F₁ ≃+* F₂)
    (h : Algebra.trdeg F₁ ℂ = Algebra.trdeg F₂ ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a : F₁, σ a = e a :=
  GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq e h

end GroundTheory.Global
