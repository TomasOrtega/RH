import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem clopen_pre_inj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C D : Set (PrimeSpectrum B)} (hC : IsClopen C) (hD : IsClopen D)
    (hCD : PrimeSpectrum.comap φ ⁻¹' C = PrimeSpectrum.comap φ ⁻¹' D) : C = D := by
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC
  obtain ⟨d, hd, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hD
  have h1 : φ e = φ d := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem (he.map φ) (hd.map φ)
    apply SetLike.coe_injective
    rw [← PrimeSpectrum.comap_basicOpen, ← PrimeSpectrum.comap_basicOpen]
    exact hCD
  rw [(h (φ e) (he.map φ)).unique ⟨he, rfl⟩ ⟨hd, h1.symm⟩]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem clopen_pre_surj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C' : Set (PrimeSpectrum B')} (hC' : IsClopen C') :
    ∃ C : Set (PrimeSpectrum B), IsClopen C ∧ PrimeSpectrum.comap φ ⁻¹' C = C' := by
  obtain ⟨e', he', rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC'
  obtain ⟨e, ⟨he, rfl⟩, -⟩ := h e' he'
  exact ⟨_, PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.locallyConstant_comap_bijective :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B') (Y : Type), (∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e') → Function.Bijective (fun a : LocallyConstant (PrimeSpectrum B) Y => a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) := by
  intro B B' _ _ φ Y h
  constructor
  · intro a b hab
    have hfib : ∀ y, (a : PrimeSpectrum B → Y) ⁻¹' {y} = (b : PrimeSpectrum B → Y) ⁻¹' {y} := by
      intro y
      apply clopen_pre_inj φ h (a.isLocallyConstant.isClopen_fiber y)
        (b.isLocallyConstant.isClopen_fiber y)
      ext q
      have hq : a (PrimeSpectrum.comap φ q) = b (PrimeSpectrum.comap φ q) :=
        DFunLike.congr_fun hab q
      change a (PrimeSpectrum.comap φ q) = y ↔ b (PrimeSpectrum.comap φ q) = y
      rw [hq]
    ext p
    have hp : p ∈ (b : PrimeSpectrum B → Y) ⁻¹' {a p} := by
      rw [← hfib]
      rfl
    exact hp.symm
  · intro a'
    choose C hCc hC using fun y =>
      clopen_pre_surj φ h (a'.isLocallyConstant.isClopen_fiber y)
    have hdisj : ∀ y z, y ≠ z → C y ∩ C z = ∅ := by
      intro y z hyz
      apply clopen_pre_inj φ h ((hCc y).inter (hCc z)) isClopen_empty
      rw [Set.preimage_inter, hC, hC, Set.preimage_empty]
      ext q
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => hyz (h1.symm.trans h2)
    have hcov : (⋃ y ∈ Set.range a', C y) = Set.univ := by
      apply clopen_pre_inj φ h
        (a'.range_finite.isClopen_biUnion fun y _ => hCc y) isClopen_univ
      rw [Set.preimage_iUnion₂, Set.preimage_univ]
      ext q
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨a' q, ⟨q, rfl⟩, by rw [hC]; rfl⟩
    have hex : ∀ p, ∃ y, p ∈ C y := by
      intro p
      have hp : p ∈ ⋃ y ∈ Set.range a', C y := hcov ▸ Set.mem_univ p
      obtain ⟨y, -, hy⟩ := Set.mem_iUnion₂.1 hp
      exact ⟨y, hy⟩
    choose a ha using hex
    have hiff : ∀ p y, a p = y ↔ p ∈ C y := by
      intro p y
      constructor
      · rintro rfl
        exact ha p
      · intro hy
        by_contra hne
        have : p ∈ C (a p) ∩ C y := ⟨ha p, hy⟩
        rw [hdisj _ _ hne] at this
        exact this
    have hlc : IsLocallyConstant a := by
      refine (IsLocallyConstant.iff_isOpen_fiber).2 fun y => ?_
      have : a ⁻¹' {y} = C y := by
        ext p
        exact hiff p y
      rw [this]
      exact (hCc y).isOpen
    refine ⟨⟨a, hlc⟩, ?_⟩
    ext q
    have hq : q ∈ PrimeSpectrum.comap φ ⁻¹' C (a' q) := by
      rw [hC]
      rfl
    exact (hiff _ _).2 hq
