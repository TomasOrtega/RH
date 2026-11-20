import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

/- English proof (translation)
Use `IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_` and prove the remaining obligations. Establish `hdeg : p.degree ≠ 0` using `fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)`. Take `⟨r, hr⟩` from `IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L) p hdeg`. Use `haveI : Algebra.IsAlgebraic K (AlgebraicClosure L) := Algebra.IsAlgebraic.trans K L _`. Use `haveI : IsPurelyInseparable L (AlgebraicClosure L) := IsPurelyInseparable.tower_top K L (AlgebraicClosure L)`.

Establish `hs : IsSeparable L r` using `Polynomial.Separable.of_dvd hsep (minpoly.dvd L r hr)`. Take `⟨x, rfl⟩` from `IsPurelyInseparable.inseparable' r hs`. Use `⟨x, (algebraMap L (AlgebraicClosure L)).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, ← hr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]`.
-/
private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : p.degree ≠ 0 := fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L) p hdeg
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L) := Algebra.IsAlgebraic.trans K L _
  haveI : IsPurelyInseparable L (AlgebraicClosure L) :=
    IsPurelyInseparable.tower_top K L (AlgebraicClosure L)
  have hs : IsSeparable L r := Polynomial.Separable.of_dvd hsep (minpoly.dvd L r hr)
  obtain ⟨x, rfl⟩ := IsPurelyInseparable.inseparable' r hs
  refine ⟨x, (algebraMap L (AlgebraicClosure L)).injective ?_⟩
  rw [map_zero, ← hr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

/- English proof (translation)
Take `⟨hH, hS⟩` from `hO`. Use `haveI := hH`. Use `haveI := hT`. Use `⟨hT, ?_⟩` and prove the remaining obligations. Use `haveI : IsLocalHom (algebraMap O T) := ⟨fun a ha => by`.

Assume the negation of the conclusion as `h`. Establish `h1 : a ∈ IsLocalRing.maximalIdeal O` using `h`. Rewrite `h1` using `[← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T)]`. Conclude with `(Ideal.mem_comap.1 h1) ha⟩`. Use `letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := (IsLocalRing.ResidueField.map (algebraMap O T)).toAlgebra`.

Use `haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := by`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `IsLocalRing.residue_surjective x`. Take `⟨p, hp, h0⟩` from `Algebra.IsIntegral.isIntegral (R := O) t`. Use `IsIntegral.isAlgebraic ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map]`. Establish `h2 : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)).comp (IsLocalRing.residue O) = (IsLocalRing.residue T).comp (algebraMap O T)` using `rfl`. Rewrite using `[h2, ← Polynomial.hom_eval₂, h0, map_zero]`. Conclude with `sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) _`.
-/
private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨hH, hS⟩ := hO
  haveI := hH
  haveI := hT
  refine ⟨hT, ?_⟩
  haveI : IsLocalHom (algebraMap O T) := ⟨fun a ha => by
    by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal O := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T)] at h1
    exact (Ideal.mem_comap.1 h1) ha⟩
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) :=
    (IsLocalRing.ResidueField.map (algebraMap O T)).toAlgebra
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨p, hp, h0⟩ := Algebra.IsIntegral.isIntegral (R := O) t
    refine IsIntegral.isAlgebraic ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h2 : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)).comp
        (IsLocalRing.residue O) = (IsLocalRing.residue T).comp (algebraMap O T) := rfl
    rw [h2, ← Polynomial.hom_eval₂, h0, map_zero]
  exact sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) _

/- English proof (translation)
Take `⟨s⟩` from `hS T (T ⊗[B] C) hT`. Use `⟨s.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom, fun b => ?_⟩` and prove the remaining obligations. Establish `h1 : (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b) = algebraMap T (T ⊗[B] C) (algebraMap B T b)`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply B T (T ⊗[B] C)]`. Express the relevant statement in the definitionally equal form `s ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b)) = _`.

Rewrite using `[h1]`. Conclude with `s.commutes _`.
-/
private theorem exists_ringHom (hS : SHSec) (B C T : Type) [CommRing B] [CommRing C] [CommRing T]
    [Algebra B C] [Algebra.Etale B C] [Module.FaithfullyFlat B C] [Algebra B T] (hT : SH T) :
    ∃ f : C →+* T, ∀ b, f (algebraMap B C b) = algebraMap B T b := by
  obtain ⟨s⟩ := hS T (T ⊗[B] C) hT
  refine ⟨s.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom, fun b => ?_⟩
  have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b) =
      algebraMap T (T ⊗[B] C) (algebraMap B T b) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B T (T ⊗[B] C)]
  change s ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b)) = _
  rw [h1]
  exact s.commutes _

end UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

open UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable in
/- English proof (translation)
Introduce `hS O B C _ _ _ _ _ _ _ _ hO`. Take `⟨hH, -⟩` from `id hO`. Use `haveI := hH`. Take `⟨ι, _, T, _, _, e, hT⟩` from `GlobalTheory.exists_algEquiv_pi_henselianLocalRing O B`. Establish `key : ∀ i, ∃ f : C →+* T i, ∀ b, f (algebraMap B C b) = e b i`.

Introduce `i`. Use `haveI := (hT i).2`. Establish `hs` using `sh_of_finite O (T i) hO (hT i).1`. Use `letI : Algebra B (T i) := ((Pi.evalRingHom T i).comp (e : B →+* Π i, T i)).toAlgebra`. Conclude with `exists_ringHom hS B C (T i) hs`.

Use `choose f hf using key`. Use `⟨{ toRingHom := (e.symm : (Π i, T i) →+* B).comp (Pi.ringHom f), commutes' := fun b => ?_ }⟩` and prove the remaining obligations. Establish `h : Pi.ringHom f (algebraMap B C b) = e b` using `funext fun i => hf i b`. Express the relevant statement in the definitionally equal form `e.symm (Pi.ringHom f (algebraMap B C b)) = b`. Rewrite using `[h]`.

Conclude with `e.symm_apply_apply b`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.finSec_of :
    SHSec → FinSec := by
  intro hS O B C _ _ _ _ _ _ _ _ hO
  obtain ⟨hH, -⟩ := id hO
  haveI := hH
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O B
  have key : ∀ i, ∃ f : C →+* T i, ∀ b, f (algebraMap B C b) = e b i := by
    intro i
    haveI := (hT i).2
    have hs := sh_of_finite O (T i) hO (hT i).1
    letI : Algebra B (T i) := ((Pi.evalRingHom T i).comp (e : B →+* Π i, T i)).toAlgebra
    exact exists_ringHom hS B C (T i) hs
  choose f hf using key
  refine ⟨{ toRingHom := (e.symm : (Π i, T i) →+* B).comp (Pi.ringHom f), commutes' := fun b => ?_ }⟩
  have h : Pi.ringHom f (algebraMap B C b) = e b := funext fun i => hf i b
  change e.symm (Pi.ringHom f (algebraMap B C b)) = b
  rw [h]
  exact e.symm_apply_apply b
