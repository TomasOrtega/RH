import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.PicLoc

open Algebra in

/- English proof (translation)
Use `letI : Algebra K R := localizationAlgebra S A'`. Use `haveI : IsScalarTower B K R := isScalarTower_localizationAlgebra S A'`. Use `haveI : FormallyEtale A' R := FormallyEtale.of_isLocalization (algebraMapSubmonoid A' S)`. Use `haveI : FormallyUnramified B R := FormallyUnramified.comp B A' R`. Use `haveI : FormallyUnramified K R := FormallyUnramified.of_restrictScalars B K R`.

Use `haveI : EssFiniteType A' R := EssFiniteType.of_isLocalization R (algebraMapSubmonoid A' S)`. Use `haveI : EssFiniteType B R := EssFiniteType.comp B A' R`. Use `haveI : EssFiniteType K R := EssFiniteType.of_comp B K R`. Use `haveI : Module.Finite K R := FormallyUnramified.finite_of_free K R`. Use `haveI : IsArtinianRing R := IsArtinianRing.of_finite K R`.

Use `infer_instance`.
-/
theorem finite_maximalSpectrum_of_field (B : Type) [CommRing B] (S : Submonoid B) (K : Type)
    [Field K] [Algebra B K] [IsLocalization S K] (A' : Type) [CommRing A'] [Algebra B A']
    [FormallyUnramified B A'] [FiniteType B A'] (R : Type) [CommRing R] [Algebra A' R]
    [IsLocalization (algebraMapSubmonoid A' S) R] [Algebra B R] [IsScalarTower B A' R] :
    Finite (MaximalSpectrum R) := by
  letI : Algebra K R := localizationAlgebra S A'
  haveI : IsScalarTower B K R := isScalarTower_localizationAlgebra S A'
  haveI : FormallyEtale A' R := FormallyEtale.of_isLocalization (algebraMapSubmonoid A' S)
  haveI : FormallyUnramified B R := FormallyUnramified.comp B A' R
  haveI : FormallyUnramified K R := FormallyUnramified.of_restrictScalars B K R
  haveI : EssFiniteType A' R := EssFiniteType.of_isLocalization R (algebraMapSubmonoid A' S)
  haveI : EssFiniteType B R := EssFiniteType.comp B A' R
  haveI : EssFiniteType K R := EssFiniteType.of_comp B K R
  haveI : Module.Finite K R := FormallyUnramified.finite_of_free K R
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  infer_instance

/- English proof (translation)
Use `set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS`. Use `haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors h0)`. Establish `hbot : ∀ Q : Ideal (Localization S), Q.IsPrime → Q = ⊥`. Introduce `Q hQ`. Use `set p := Q.comap (algebraMap B (Localization S)) with hp`.

Use `haveI : p.IsPrime := Ideal.comap_isPrime _ Q`. Establish `hdisj : ∀ s ∈ S, s ∉ p`. Introduce `s hs hsp`. Conclude with `hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp (IsLocalization.map_units (Localization S) ⟨s, hs⟩))`. Establish `hp0 : p = ⊥`.

Assume the negation of the conclusion as `hne`. Establish `hmax : p.IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hne`. Establish `hf : f ∉ p` using `fun h => hdisj f (Submonoid.mem_sup_right (Submonoid.mem_powers f)) h`. Establish `htop : p ⊔ Ideal.span {f} = ⊤`. Use `hmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hf ?_)` and prove the remaining obligations.

Rewrite using `[h]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : B) ∈ p ⊔ Ideal.span {f})`. Establish `hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a)`. Establish `hb0 : Ideal.Quotient.mk (Ideal.span {f}) b = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hb`.

Establish `: Ideal.Quotient.mk (Ideal.span {f}) a = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span {f})), ← hab, map_add, hb0, add_zero]`. Rewrite using `[this]`. Conclude with `isUnit_one`. Conclude with `hdisj a (Submonoid.mem_sup_left hunit) ha`.

Rewrite using `[← IsLocalization.map_under S (Localization S) Q]`. Express the relevant statement in the definitionally equal form `Ideal.map _ p = ⊥`. Rewrite using `[hp0, Ideal.map_bot]`. Use `haveI : Ring.KrullDimLE 0 (Localization S) := by`. Rewrite using `[Ring.krullDimLE_zero_iff]`.

Introduce `I hI`. Take `⟨m, hm, -⟩` from `Ideal.exists_le_maximal (⊥ : Ideal (Localization S)) bot_ne_top`. Rewrite using `[hbot I hI, ← hbot m hm.isPrime]`. Conclude with `hm`. Conclude with `Ring.KrullDimLE.isField_of_isDomain`.
-/
theorem isField_localization (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (h0 : (0 : B) ∉ (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f) :
    IsField (Localization ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)) := by
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  haveI : IsDomain (Localization S) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors h0)

  have hbot : ∀ Q : Ideal (Localization S), Q.IsPrime → Q = ⊥ := by
    intro Q hQ
    set p := Q.comap (algebraMap B (Localization S)) with hp
    haveI : p.IsPrime := Ideal.comap_isPrime _ Q
    have hdisj : ∀ s ∈ S, s ∉ p := by
      intro s hs hsp
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp
        (IsLocalization.map_units (Localization S) ⟨s, hs⟩))
    have hp0 : p = ⊥ := by
      by_contra hne
      have hmax : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
      have hf : f ∉ p := fun h => hdisj f (Submonoid.mem_sup_right (Submonoid.mem_powers f)) h
      have htop : p ⊔ Ideal.span {f} = ⊤ := by
        refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hf ?_)
        rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : B) ∈ p ⊔ Ideal.span {f})
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a) := by
        have hb0 : Ideal.Quotient.mk (Ideal.span {f}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
        have : Ideal.Quotient.mk (Ideal.span {f}) a = 1 := by
          rw [← map_one (Ideal.Quotient.mk (Ideal.span {f})), ← hab, map_add, hb0, add_zero]
        rw [this]; exact isUnit_one
      exact hdisj a (Submonoid.mem_sup_left hunit) ha
    rw [← IsLocalization.map_under S (Localization S) Q]
    change Ideal.map _ p = ⊥
    rw [hp0, Ideal.map_bot]
  haveI : Ring.KrullDimLE 0 (Localization S) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (Localization S)) bot_ne_top
    rw [hbot I hI, ← hbot m hm.isPrime]
    exact hm
  exact Ring.KrullDimLE.isField_of_isDomain

end GlobalTheory.PicLoc

namespace GlobalTheory.PicLoc

/- English proof (translation)
Introduce `B _ _ f A' _ _ _`. Use `set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS`. It suffices to establish `Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) from inferInstance`. Distinguish the cases in `h0 : (0 : B) ∈ S`. Establish `h0' : (0 : A') ∈ Algebra.algebraMapSubmonoid A' S` using `Submonoid.mem_map.2 ⟨0, h0, map_zero _⟩`.

Use `letI := IsLocalization.uniqueOfZeroMem (S := Localization (Algebra.algebraMapSubmonoid A' S)) h0'`. Use `haveI : IsEmpty (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) := ⟨fun m => m.isMaximal.ne_top (by`. Rewrite using `[Ideal.eq_top_iff_one, Subsingleton.elim (1 : Localization _) 0]`. Conclude with `m.asIdeal.zero_mem)⟩`. Use `infer_instance`.

Use `letI : Field (Localization S) := (isField_localization B f h0).toField`. Conclude with `finite_maximalSpectrum_of_field B S (Localization S) A' (Localization (Algebra.algebraMapSubmonoid A' S))`.
-/
theorem subsingleton_pic_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  intro B _ _ f A' _ _ _
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  suffices Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) from
    inferInstance
  by_cases h0 : (0 : B) ∈ S
  · have h0' : (0 : A') ∈ Algebra.algebraMapSubmonoid A' S :=
      Submonoid.mem_map.2 ⟨0, h0, map_zero _⟩
    letI := IsLocalization.uniqueOfZeroMem
      (S := Localization (Algebra.algebraMapSubmonoid A' S)) h0'
    haveI : IsEmpty (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) :=
      ⟨fun m => m.isMaximal.ne_top (by
        rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Localization _) 0]
        exact m.asIdeal.zero_mem)⟩
    infer_instance
  · letI : Field (Localization S) := (isField_localization B f h0).toField
    exact finite_maximalSpectrum_of_field B S (Localization S) A'
      (Localization (Algebra.algebraMapSubmonoid A' S))

end GlobalTheory.PicLoc
