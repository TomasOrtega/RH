import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
Take `⟨e, he, rfl⟩` from `PrimeSpectrum.isClopen_iff.1 hC`. Take `⟨d, hd, rfl⟩` from `PrimeSpectrum.isClopen_iff.1 hD`. Establish `h1 : φ e = φ d`. Apply `PrimeSpectrum.basicOpen_injOn_isIdempotentElem (he.map φ) (hd.map φ)` to reduce the goal to its premises. Apply `SetLike.coe_injective` to reduce the goal to its premises.

Rewrite using `[← PrimeSpectrum.comap_basicOpen, ← PrimeSpectrum.comap_basicOpen]`. Conclude with `hCD`. Rewrite using `[(h (φ e) (he.map φ)).unique ⟨he, rfl⟩ ⟨hd, h1.symm⟩]`.
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
Take `⟨e', he', rfl⟩` from `PrimeSpectrum.isClopen_iff.1 hC'`. Take `⟨e, ⟨he, rfl⟩, -⟩` from `h e' he'`. Conclude with `⟨_, PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩, rfl⟩`.
-/
private theorem clopen_pre_surj {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : ∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e')
    {C' : Set (PrimeSpectrum B')} (hC' : IsClopen C') :
    ∃ C : Set (PrimeSpectrum B), IsClopen C ∧ PrimeSpectrum.comap φ ⁻¹' C = C' := by
  obtain ⟨e', he', rfl⟩ := PrimeSpectrum.isClopen_iff.1 hC'
  obtain ⟨e, ⟨he, rfl⟩, -⟩ := h e' he'
  exact ⟨_, PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩, rfl⟩

/- English proof (translation)
Introduce `B B' _ _ φ Y h`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Establish `hfib : ∀ y, (a : PrimeSpectrum B → Y) ⁻¹' {y} = (b : PrimeSpectrum B → Y) ⁻¹' {y}`. Introduce `y`.

Apply `clopen_pre_inj φ h (a.isLocallyConstant.isClopen_fiber y) (b.isLocallyConstant.isClopen_fiber y)` to reduce the goal to its premises. Use extensionality with `q`. Establish `hq : a (PrimeSpectrum.comap φ q) = b (PrimeSpectrum.comap φ q)` using `DFunLike.congr_fun hab q`. Express the relevant statement in the definitionally equal form `a (PrimeSpectrum.comap φ q) = y ↔ b (PrimeSpectrum.comap φ q) = y`. Rewrite using `[hq]`.

Use extensionality with `p`. Establish `hp : p ∈ (b : PrimeSpectrum B → Y) ⁻¹' {a p}`. Rewrite using `[← hfib]`. Both sides reduce to the same expression. Conclude with `hp.symm`.

Introduce `a' choose C hCc hC using fun y => clopen_pre_surj φ h (a'.isLocallyConstant.isClopen_fiber y)`. Establish `hdisj : ∀ y z, y ≠ z → C y ∩ C z = ∅`. Introduce `y z hyz`. Apply `clopen_pre_inj φ h ((hCc y).inter (hCc z)) isClopen_empty` to reduce the goal to its premises. Rewrite using `[Set.preimage_inter, hC, hC, Set.preimage_empty]`.

Use extensionality with `q`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Conclude with `fun h1 h2 => hyz (h1.symm.trans h2)`. Establish `hcov : (⋃ y ∈ Set.range a', C y) = Set.univ`. Apply `clopen_pre_inj φ h (a'.range_finite.isClopen_biUnion fun y _ => hCc y) isClopen_univ` to reduce the goal to its premises.

Rewrite using `[Set.preimage_iUnion₂, Set.preimage_univ]`. Use extensionality with `q`. Simplify using `only [Set.mem_iUnion, Set.mem_univ, iff_true]`. Conclude with `⟨a' q, ⟨q, rfl⟩, by rw [hC]; rfl⟩`. Establish `hex : ∀ p, ∃ y, p ∈ C y`.

Introduce `p`. Establish `hp : p ∈ ⋃ y ∈ Set.range a', C y` using `hcov ▸ Set.mem_univ p`. Take `⟨y, -, hy⟩` from `Set.mem_iUnion₂.1 hp`. Conclude with `⟨y, hy⟩`. Use `choose a ha using hex`.

Establish `hiff : ∀ p y, a p = y ↔ p ∈ C y`. Introduce `p y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `ha p`.

Introduce `hy`. Assume the negation of the conclusion as `hne`. Establish `: p ∈ C (a p) ∩ C y` using `⟨ha p, hy⟩`. Rewrite `this` using `[hdisj _ _ hne]`. Conclude with `this`.

Establish `hlc : IsLocallyConstant a`. Use `(IsLocallyConstant.iff_isOpen_fiber).2 fun y => ?_` and prove the remaining obligations. Establish `: a ⁻¹' {y} = C y`. Use extensionality with `p`. Conclude with `hiff p y`.

Rewrite using `[this]`. Conclude with `(hCc y).isOpen`. Use `⟨⟨a, hlc⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `q`. Establish `hq : q ∈ PrimeSpectrum.comap φ ⁻¹' C (a' q)`.

Rewrite using `[hC]`. Both sides reduce to the same expression. Conclude with `(hiff _ _).2 hq`.
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
