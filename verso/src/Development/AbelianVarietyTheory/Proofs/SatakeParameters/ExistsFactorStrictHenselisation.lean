import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmpBijectiveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.FormalInv.Fib GlobalTheory.NCyc

namespace GlobalTheory.StrictHensFactor

/- English proof (translation)
Introduce `A C B _ _ _ _ _ _ _ _ _ u`. Use `set P : Ideal C := (maximalIdeal B).comap (u : C →+* B) with hP`. Use `haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _`. Set `L` to `Localization.AtPrime P`. Establish `hu : ∀ y : P.primeCompl, IsUnit ((u : C →+* B) y)`.

Introduce `y`. Use `y.2` as an intermediate fact. Assume the negation of the conclusion as `hy`. Conclude with `this ((IsLocalRing.mem_maximalIdeal _).2 hy)`. Set `b : L →+* B` to `IsLocalization.lift hu`.

Establish `hb : b.comp (algebraMap C L) = (u : C →+* B)` using `IsLocalization.lift_comp hu`. Use `haveI hbloc : IsLocalHom b := by`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl x`. Rewrite using `[IsLocalization.AtPrime.isUnit_mk'_iff]`.

Introduce `ha`. Establish `h1 : (u : C →+* B) a = (u : C →+* B) s * b (IsLocalization.mk' _ a s)` using `(IsLocalization.lift_mk'_spec _ _ _ _).1 rfl`. Establish `h2 : IsUnit ((u : C →+* B) a)`. Rewrite using `[h1]`. Conclude with `(hu s).mul hx`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 ha h2`. Take `⟨S, _, _, _, hloc, hsc, -, -, -, ι, _, _, _, Si, hmono, hcov, hA⟩` from `GlobalTheory.exists_strictHenselisation L (SeparableClosure (ResidueField L))`. Establish `hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S)`. Use `GlobalTheory.StrictHensUnion.indEtale_of_directed_union L S ι Si hmono hcov fun i => ?_` and prove the remaining obligations. Take `⟨A', _, _, _, q, _, ⟨e⟩⟩` from `hA i`.

Conclude with `GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale L A' q.primeCompl)`. Establish `hstrict : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap L S)` using `⟨inferInstance, hsc, hloc, hind⟩`. Take `⟨g, hg⟩` from `GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation (algebraMap L S) hstrict b`. Set `cR : C →+* S` to `(algebraMap L S).comp (algebraMap C L)`. Use `letI algAS : Algebra A S := (cR.comp (algebraMap A C)).toAlgebra`.

Set `c : C →ₐ[A] S` to `{ cR with commutes' := fun a => rfl }`. Establish `hgc : g.comp cR = (u : C →+* B)`. Rewrite using `[← RingHom.comp_assoc, hg, hb]`. Set `w : S →ₐ[A] B` to `{ g with commutes' := fun a => by`. Express the relevant statement in the definitionally equal form `g (cR (algebraMap A C a)) = algebraMap A B a`.

Rewrite using `[← RingHom.comp_apply, hgc]`. Conclude with `u.commutes a }`. Use `⟨S, inferInstance, inferInstance, algAS, c, w, ?_, P, hPp, algebraMap L S, hstrict, rfl, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `DFunLike.congr_fun hgc x`.

Use extensionality with `a`. Rewrite using `[hP, Ideal.comap_comap, Ideal.mem_comap]`. Establish `: ((u : C →+* B).comp (algebraMap A C)) a = algebraMap A B a` using `u.commutes a`. Rewrite using `[this, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]`.
-/
theorem exists_factor_strictHenselisation : ∀ (A C B : Type) [CommRing A] [IsLocalRing A] [CommRing C] [Algebra A C] [CommRing B] [HenselianLocalRing B] [IsSepClosed (ResidueField B)] [Algebra A B] [IsLocalHom (algebraMap A B)] (u : C →ₐ[A] B), ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : Algebra A D) (c : C →ₐ[A] D) (w : D →ₐ[A] B), w.comp c = u ∧ ∃ (P : Ideal C) (_ : P.IsPrime) (φ : Localization.AtPrime P →+* D), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ ∧ φ.comp (algebraMap C (Localization.AtPrime P)) = (c : C →+* D) ∧ P.comap (algebraMap A C) = maximalIdeal A := by
  intro A C B _ _ _ _ _ _ _ _ _ u
  set P : Ideal C := (maximalIdeal B).comap (u : C →+* B) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit ((u : C →+* B) y) := by
    intro y
    have := y.2
    by_contra hy
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let b : L →+* B := IsLocalization.lift hu
  have hb : b.comp (algebraMap C L) = (u : C →+* B) := IsLocalization.lift_comp hu
  haveI hbloc : IsLocalHom b := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro ha
    have h1 : (u : C →+* B) a = (u : C →+* B) s * b (IsLocalization.mk' _ a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have h2 : IsUnit ((u : C →+* B) a) := by
      rw [h1]; exact (hu s).mul hx
    exact (IsLocalRing.mem_maximalIdeal _).1 ha h2
  obtain ⟨S, _, _, _, hloc, hsc, -, -, -, ι, _, _, _, Si, hmono, hcov, hA⟩ :=
    GlobalTheory.exists_strictHenselisation L (SeparableClosure (ResidueField L))
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union L S ι Si hmono hcov fun i => ?_
    obtain ⟨A', _, _, _, q, _, ⟨e⟩⟩ := hA i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale L A' q.primeCompl)
  have hstrict : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap L S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  obtain ⟨g, hg⟩ := GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation
    (algebraMap L S) hstrict b
  let cR : C →+* S := (algebraMap L S).comp (algebraMap C L)
  letI algAS : Algebra A S := (cR.comp (algebraMap A C)).toAlgebra
  let c : C →ₐ[A] S := { cR with commutes' := fun a => rfl }
  have hgc : g.comp cR = (u : C →+* B) := by
    rw [← RingHom.comp_assoc, hg, hb]
  let w : S →ₐ[A] B :=
    { g with
      commutes' := fun a => by
        change g (cR (algebraMap A C a)) = algebraMap A B a
        rw [← RingHom.comp_apply, hgc]
        exact u.commutes a }
  refine ⟨S, inferInstance, inferInstance, algAS, c, w, ?_, P, hPp, algebraMap L S, hstrict, rfl, ?_⟩
  · ext x
    exact DFunLike.congr_fun hgc x
  · ext a
    rw [hP, Ideal.comap_comap, Ideal.mem_comap]
    have : ((u : C →+* B).comp (algebraMap A C)) a = algebraMap A B a := u.commutes a
    rw [this, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory.StrictHensFactor
