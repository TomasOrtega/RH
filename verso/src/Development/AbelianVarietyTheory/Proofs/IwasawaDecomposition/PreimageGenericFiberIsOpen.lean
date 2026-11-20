import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFibreOpen

/- English proof (translation)
Establish `key : ∀ y : Sp K, ((spMap (algebraMap O K)).base y : PrimeSpectrum O).asIdeal = ⊥` using `fun y => by`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O K) (y : PrimeSpectrum K).asIdeal = ⊥`. Rewrite using `[(Ideal.eq_bot_or_top (y : PrimeSpectrum K).asIdeal).resolve_right (y : PrimeSpectrum K).isPrime.ne_top]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `key y`. Introduce `hx`. Use `⟨(show Sp K from (default : PrimeSpectrum K)), ?_⟩` and prove the remaining obligations.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `(key _).trans hx.symm`.
-/
theorem range_spMap_algebraMap_eq (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Set.range (spMap (algebraMap O K)) = {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} := by
  have key : ∀ y : Sp K, ((spMap (algebraMap O K)).base y : PrimeSpectrum O).asIdeal = ⊥ := fun y => by
    change Ideal.comap (algebraMap O K) (y : PrimeSpectrum K).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top (y : PrimeSpectrum K).asIdeal).resolve_right (y : PrimeSpectrum K).isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · intro hx
    refine ⟨(show Sp K from (default : PrimeSpectrum K)), ?_⟩
    apply PrimeSpectrum.ext
    exact (key _).trans hx.symm

end GlobalTheory.GenericFibreOpen

open GlobalTheory.GenericFibreOpen in

/- English proof (translation)
Introduce `O K R _ _ _ _ _ _ _ g`. Rewrite using `[range_spMap_algebraMap_eq O K]`. Establish `hc : Continuous g.base` using `g.base.hom.continuous`. Use `set c : Sp R := (IsLocalRing.closedPoint R : PrimeSpectrum R)`. Establish `hle : ∀ x : Sp R, ((g.base x : Sp O) : PrimeSpectrum O).asIdeal ≤ ((g.base c : Sp O) : PrimeSpectrum O).asIdeal`.

Introduce `x`. Establish `hs : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R` using `IsLocalRing.specializes_closedPoint _`. Conclude with `(PrimeSpectrum.le_iff_specializes _ _).2 (hs.map hc)`. Distinguish the cases in `hp : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal = ⊥`. Establish `: (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} = Set.univ`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Conclude with `le_bot_iff.1 (hp ▸ hle x)`. Conclude with `this ▸ isOpen_univ`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hp`.

Establish `hmax : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal` using `((g.base c : Sp O) : PrimeSpectrum O).isPrime.isMaximal hp`. Establish `: (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} = (fun x : Sp R => g.base x) ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum O))`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `h hx`. Rewrite `hx` using `[h, Ideal.mem_bot]`. Conclude with `ha0 hx`. Introduce `hx`. Assume the negation of the conclusion as `hne`.

Establish `hq : ((g.base x : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal` using `((g.base x : Sp O) : PrimeSpectrum O).isPrime.isMaximal hne`. Establish `heq` using `hq.eq_of_le hmax.ne_top (hle x)`. Conclude with `hx (heq ▸ ha)`. Rewrite using `[this]`. Conclude with `(PrimeSpectrum.basicOpen a).isOpen.preimage hc`.
-/
theorem GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction :
    ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R]
      [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  intro O K R _ _ _ _ _ _ _ g
  rw [range_spMap_algebraMap_eq O K]
  have hc : Continuous g.base := g.base.hom.continuous
  set c : Sp R := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  have hle : ∀ x : Sp R, ((g.base x : Sp O) : PrimeSpectrum O).asIdeal ≤ ((g.base c : Sp O) : PrimeSpectrum O).asIdeal := by
    intro x
    have hs : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
    exact (PrimeSpectrum.le_iff_specializes _ _).2 (hs.map hc)
  by_cases hp : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal = ⊥
  · have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_bot_iff.1 (hp ▸ hle x)
    exact this ▸ isOpen_univ
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    have hmax : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
      ((g.base c : Sp O) : PrimeSpectrum O).isPrime.isMaximal hp
    have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} =
        (fun x : Sp R => g.base x) ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum O)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h hx
        rw [h, Ideal.mem_bot] at hx
        exact ha0 hx
      · intro hx
        by_contra hne
        have hq : ((g.base x : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
          ((g.base x : Sp O) : PrimeSpectrum O).isPrime.isMaximal hne
        have heq := hq.eq_of_le hmax.ne_top (hle x)
        exact hx (heq ▸ ha)
    rw [this]
    exact (PrimeSpectrum.basicOpen a).isOpen.preimage hc
