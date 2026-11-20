import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsReductionModP
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

namespace ReductionModP

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Use `(hmax.eq_of_le (RingHom.ker_ne_top _) ?_).symm` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hpF`.
-/
theorem ker_intCast_eq {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hpF : ((p : ℤ) : F) = 0) :
    RingHom.ker (Int.castRingHom F) = Ideal.span {(p : ℤ)} := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine (hmax.eq_of_le (RingHom.ker_ne_top _) ?_).symm
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact hpF

/- English proof (translation)
Introduce `n p W F _ hp hW hpW hsurj hpF`. Use `set e := GenericFibreIdeal.blkRingEquiv n`. Use `set φ : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) F := MvPolynomial.map (Int.castRingHom F)`. Use `set I := (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map φ`. Establish `hφ : Function.Surjective φ` using `MvPolynomial.map_surjective _ hsurj`.

Establish `hker : RingHom.ker φ ≤ IndefiniteRowSideFullHecke.ArithBezout.finIdeal W`. Rewrite using `[MvPolynomial.ker_map, ker_intCast_eq hp hpF, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]`. Use `show rename _ (C (p : ℤ)) ∈ W`. Rewrite using `[rename_C]`. Conclude with `hpW`.

Establish `hprime : (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).IsPrime`. Use `hW.1` as an intermediate fact. Conclude with `Ideal.comap_isPrime _ _`. Establish `hcomapφ : I.comap φ = IndefiniteRowSideFullHecke.ArithBezout.finIdeal W`. Rewrite using `[Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot]`.

Conclude with `sup_eq_left.mpr hker`. Use `set ψ : MRing (PBlk n) →+* MvPolynomial (Fin n) F := φ.comp e.symm.toRingHom`. Establish `hψ : Function.Surjective ψ` using `hφ.comp e.symm.surjective`. Establish `hcomapψ : I.comap ψ = W`. Use extensionality with `x`.

Rewrite using `[← Ideal.comap_comap, hcomapφ]`. Use `show rename _ (e.symm x) ∈ W ↔ x ∈ W`. Conclude with `Iff.of_eq (congrArg (· ∈ W) (e.apply_symm_apply x))`. Establish `hX : ∀ i : Fin n, ψ (X ⟨(), i⟩) = X i` using `fun i => by show MvPolynomial.map _ ((renameEquiv ℤ (GenericFibreIdeal.blkEquiv n)).symm (X ⟨(), i⟩)) = X i`. Rewrite using `[renameEquiv_symm, renameEquiv_apply, rename_X, map_X]`.

Both sides reduce to the same expression. Establish `hmem : ∀ i : Fin n, (X i : MvPolynomial (Fin n) F) ∈ I ↔ (X ⟨(), i⟩ : MRing (PBlk n)) ∈ W` using `fun i => by rw [← hcomapψ, Ideal.mem_comap, hX]`. Establish `hg : Function.Surjective ((Ideal.Quotient.mk I).comp ψ)` using `Ideal.Quotient.mk_surjective.comp hψ`. Establish `hkerg : RingHom.ker ((Ideal.Quotient.mk I).comp ψ) = W`. Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker, hcomapψ]`.

Establish `hdim : ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ringKrullDim (MRing (PBlk n) ⧸ W)` using `ringKrullDim_eq_of_ringEquiv ((RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hkerg))`. Take `⟨-, ⟨S, hS, hWS⟩, hrel⟩` from `hW`. Establish `hH : I.IsHomogeneous (homogeneousSubmodule (Fin n) F)`. Rewrite using `[← Ideal.map_comap_of_surjective ψ hψ I, hcomapψ, hWS, Ideal.map_span]`. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, hs, rfl⟩`. Take `⟨a, ha⟩` from `hS s hs`. Use `⟨a (), (mem_homogeneousSubmodule _ _).mpr ?_⟩` and prove the remaining obligations. Establish `hs' : s.IsHomogeneous (a ())`. Introduce `m hm`.

Express the relevant statement in the definitionally equal form `Finsupp.weight (fun _ => 1) m = a ()`. Rewrite using `[← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]`. Simplify using `using ha m (mem_support_iff.mpr hm) ()`. Conclude with `(IsHomogeneous.rename_isHomogeneous hs').map _`. Take `⟨i, hi⟩` from `hrel ()`.

Use `⟨⟨Ideal.map_isPrime_of_surjective hφ hker, fun f hf k => homogeneousComponent_mem_of_mem hH hf k, ⟨i, fun h => hi ((hmem i).mp h)⟩⟩, hdim, hmem⟩` and prove the remaining obligations.
-/
theorem proof : ReductionModP.Statement := by
  intro n p W F _ hp hW hpW hsurj hpF
  set e := GenericFibreIdeal.blkRingEquiv n
  set φ : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) F := MvPolynomial.map (Int.castRingHom F)
  set I := (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map φ
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ hsurj

  have hker : RingHom.ker φ ≤ IndefiniteRowSideFullHecke.ArithBezout.finIdeal W := by
    rw [MvPolynomial.ker_map, ker_intCast_eq hp hpF, Ideal.map_le_iff_le_comap, Ideal.span_le,
      Set.singleton_subset_iff]
    show rename _ (C (p : ℤ)) ∈ W
    rw [rename_C]
    exact hpW
  have hprime : (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).IsPrime := by
    have := hW.1
    exact Ideal.comap_isPrime _ _
  have hcomapφ : I.comap φ = IndefiniteRowSideFullHecke.ArithBezout.finIdeal W := by
    rw [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hker

  set ψ : MRing (PBlk n) →+* MvPolynomial (Fin n) F := φ.comp e.symm.toRingHom
  have hψ : Function.Surjective ψ := hφ.comp e.symm.surjective
  have hcomapψ : I.comap ψ = W := by
    ext x
    rw [← Ideal.comap_comap, hcomapφ]
    show rename _ (e.symm x) ∈ W ↔ x ∈ W
    exact Iff.of_eq (congrArg (· ∈ W) (e.apply_symm_apply x))
  have hX : ∀ i : Fin n, ψ (X ⟨(), i⟩) = X i := fun i => by
    show MvPolynomial.map _ ((renameEquiv ℤ (GenericFibreIdeal.blkEquiv n)).symm (X ⟨(), i⟩)) = X i
    rw [renameEquiv_symm, renameEquiv_apply, rename_X, map_X]
    rfl
  have hmem : ∀ i : Fin n, (X i : MvPolynomial (Fin n) F) ∈ I ↔ (X ⟨(), i⟩ : MRing (PBlk n)) ∈ W :=
    fun i => by rw [← hcomapψ, Ideal.mem_comap, hX]

  have hg : Function.Surjective ((Ideal.Quotient.mk I).comp ψ) :=
    Ideal.Quotient.mk_surjective.comp hψ
  have hkerg : RingHom.ker ((Ideal.Quotient.mk I).comp ψ) = W := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hcomapψ]
  have hdim : ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ringKrullDim (MRing (PBlk n) ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv
      ((RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hkerg))

  obtain ⟨-, ⟨S, hS, hWS⟩, hrel⟩ := hW
  have hH : I.IsHomogeneous (homogeneousSubmodule (Fin n) F) := by
    rw [← Ideal.map_comap_of_surjective ψ hψ I, hcomapψ, hWS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    refine ⟨a (), (mem_homogeneousSubmodule _ _).mpr ?_⟩
    have hs' : s.IsHomogeneous (a ()) := by
      intro m hm
      change Finsupp.weight (fun _ => 1) m = a ()
      rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
      simpa using ha m (mem_support_iff.mpr hm) ()
    exact (IsHomogeneous.rename_isHomogeneous hs').map _
  obtain ⟨i, hi⟩ := hrel ()
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hker, fun f hf k => homogeneousComponent_mem_of_mem hH hf k,
    ⟨i, fun h => hi ((hmem i).mp h)⟩⟩, hdim, hmem⟩

end ReductionModP

end ObjectsChow

end GroundTheory.Heights₂.Heights
