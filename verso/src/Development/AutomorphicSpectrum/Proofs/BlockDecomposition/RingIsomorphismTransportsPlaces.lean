import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso.Places

variable {R S : Type} [CommRing R] [CommRing S]

/- English proof (translation)
Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => ⟨x, h, rfl⟩`. Introduce and unpack `⟨y, hy, e⟩`. Rewrite using `[← f.injective e]` and apply the resulting hypothesis.
-/
theorem mem_iff_apply_mem_map (f : R ≃+* S) (I : Ideal R) (x : R) :
    x ∈ I ↔ f x ∈ I.map f := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · exact fun h => ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← f.injective e]

variable [IsDedekindDomain R] [IsDedekindDomain S]

noncomputable def placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.map f
  isPrime := by
    haveI := v.isPrime
    exact Ideal.map_isPrime_of_equiv f
  ne_bot := by
    intro h
    apply v.ne_bot
    exact (Ideal.map_eq_bot_iff_of_injective f.injective).1 h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem placeMap_asIdeal (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (placeMap f v).asIdeal = v.asIdeal.map f := rfl

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[placeMap_asIdeal, placeMap_asIdeal, Ideal.map_symm]`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap]`. Conclude with `(mem_iff_apply_mem_map f _ x).symm`.
-/
theorem placeMap_symm_placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) :
    placeMap f.symm (placeMap f v) = v := by
  apply HeightOneSpectrum.ext
  rw [placeMap_asIdeal, placeMap_asIdeal, Ideal.map_symm]
  ext x
  rw [Ideal.mem_comap]
  exact (mem_iff_apply_mem_map f _ x).symm

noncomputable def placeEquiv (f : R ≃+* S) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv := placeMap_symm_placeMap f
  right_inv := placeMap_symm_placeMap f.symm

/- English proof (translation)
Introduce `F F' _ _ _ _ e`. Use `⟨RingOfIntegers.mapRingEquiv e, placeEquiv (RingOfIntegers.mapRingEquiv e), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[RingOfIntegers.mapRingEquiv_apply]`. Introduce `v x`.

Conclude with `mem_iff_apply_mem_map _ _ x`. Introduce `v x`. Express the relevant statement in the definitionally equal form `x ∈ v.asIdeal ^ 2 ↔ _ ∈ (v.asIdeal.map (RingOfIntegers.mapRingEquiv e)) ^ 2`. Rewrite using `[← Ideal.map_pow]`. Conclude with `mem_iff_apply_mem_map _ _ x`.

Introduce `v`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm`.
-/
theorem exists_places_of_ringEquiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  intro F F' _ _ _ _ e
  refine ⟨RingOfIntegers.mapRingEquiv e, placeEquiv (RingOfIntegers.mapRingEquiv e), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [RingOfIntegers.mapRingEquiv_apply]
  · intro v x
    exact mem_iff_apply_mem_map _ _ x
  · intro v x
    change x ∈ v.asIdeal ^ 2 ↔ _ ∈ (v.asIdeal.map (RingOfIntegers.mapRingEquiv e)) ^ 2
    rw [← Ideal.map_pow]
    exact mem_iff_apply_mem_map _ _ x
  · intro v
    exact (Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

end GlobalTheory.CompanionTheory.PTIso.Places
