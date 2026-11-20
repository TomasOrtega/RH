import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFibreOpen

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
