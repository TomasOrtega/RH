import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `haveI : Module.Flat A R := hφ`. Use `haveI : IsLocalHom (algebraMap A R) := ‹_›`. Use `haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := R)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Establish `h` using `Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := R) ⊥`. Rewrite `h` using `[Ideal.map_bot]`. Establish `: a ∈ Ideal.comap (algebraMap A R) ⊥` using `by rw [Ideal.mem_comap, Ideal.mem_bot]; exact ha`. Rewrite `this` using `[h]`.

Simplify using `using this`.
-/
theorem injective_of_flat_local {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hφ : φ.Flat) [IsLocalHom φ] : Function.Injective φ := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : IsLocalHom (algebraMap A R) := ‹_›
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := R)
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := R) ⊥
  rw [Ideal.map_bot] at h
  have : a ∈ Ideal.comap (algebraMap A R) ⊥ := by rw [Ideal.mem_comap, Ideal.mem_bot]; exact ha
  rw [h] at this
  simpa using this

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `: φ a ∈ maximalIdeal R` using `h ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)`. Conclude with `(mem_maximalIdeal _).1 this ha`.
-/
theorem isLocalHom_of_map_maximalIdeal {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (h : (maximalIdeal A).map φ = maximalIdeal R) : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have : φ a ∈ maximalIdeal R := h ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
  exact (mem_maximalIdeal _).1 this ha

/- English proof (translation)
Take `⟨hf, hrad⟩` from `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA`. Establish `key` using `(IsDiscreteValuationRing.TFAE A hf).out 0 3`. Apply the tactic sequence `try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key`. Use `key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(isField_iff_maximalIdeal_eq).not.1 hf`.

Conclude with `(maximalIdeal.isMaximal A).isPrime`. Introduce and unpack `P ⟨hP, hPp⟩`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Use `le_antisymm (le_maximalIdeal hPp.ne_top) ?_` and prove the remaining obligations. Use `(hrad x hx0).trans ?_` and prove the remaining obligations.

Rewrite using `[hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]`. Conclude with `hxP`.
-/
theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 0 3
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

/- English proof (translation)
Introduce `A R _ _ _ _ _ _ _ _ φ hA hφ hR`. Take `⟨hfl, hm, -⟩` from `hφ`. Take `⟨hRn, -, hRc, hR0⟩` from `hR`. Use `haveI := hRn`. Use `haveI := isLocalHom_of_map_maximalIdeal φ hm`.

Establish `hinj` using `injective_of_flat_local φ hfl`. Use `haveI := isDVR_of_ringKrullDim_eq_one hA`. Establish `hAf : ¬IsField A` using `(isField_iff_maximalIdeal_eq).not.2 (IsDiscreteValuationRing.not_a_field A)`. Establish `keyA` using `(IsDiscreteValuationRing.TFAE A hAf).out 0 4`. Apply the tactic sequence `try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyA`.

Take `⟨π, hπ⟩` from `(keyA.1 inferInstance).principal`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `IsDiscreteValuationRing.not_a_field A (by rw [hπ]; simp)`. Establish `hmR : maximalIdeal R = Ideal.span {φ π}`.

Rewrite using `[← hm, hπ]`. Use `show Ideal.map φ (Ideal.span {π}) = _`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Establish `hnf : ¬IsField R`. Rewrite using `[isField_iff_maximalIdeal_eq, hmR, Ideal.span_singleton_eq_bot]`.

Conclude with `(map_ne_zero_iff φ hinj).2 hπ0`. Use `⟨?_, hRc, hR0⟩` and prove the remaining obligations. Establish `keyR` using `(IsDiscreteValuationRing.TFAE R hnf).out 0 4`. Apply the tactic sequence `try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyR`. Conclude with `keyR.2 ⟨⟨φ π, by rw [hmR]⟩⟩`.
-/
theorem cdvr_of_isEtaleCompletion : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsDomain R] [IsLocalRing R] (φ : A →+* R), ringKrullDim A = 1 →
    IsEtaleCompletion φ → IsCN R → CDvr R := by
  intro A R _ _ _ _ _ _ _ _ φ hA hφ hR
  obtain ⟨hfl, hm, -⟩ := hφ
  obtain ⟨hRn, -, hRc, hR0⟩ := hR
  haveI := hRn
  haveI := isLocalHom_of_map_maximalIdeal φ hm
  have hinj := injective_of_flat_local φ hfl
  haveI := isDVR_of_ringKrullDim_eq_one hA
  have hAf : ¬IsField A := (isField_iff_maximalIdeal_eq).not.2 (IsDiscreteValuationRing.not_a_field A)
  have keyA := (IsDiscreteValuationRing.TFAE A hAf).out 0 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyA
  obtain ⟨π, hπ⟩ := (keyA.1 inferInstance).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field A (by rw [hπ]; simp)
  have hmR : maximalIdeal R = Ideal.span {φ π} := by
    rw [← hm, hπ]
    show Ideal.map φ (Ideal.span {π}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬IsField R := by
    rw [isField_iff_maximalIdeal_eq, hmR, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff φ hinj).2 hπ0
  refine ⟨?_, hRc, hR0⟩
  have keyR := (IsDiscreteValuationRing.TFAE R hnf).out 0 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyR
  exact keyR.2 ⟨⟨φ π, by rw [hmR]⟩⟩

end GlobalTheory.CdvrExt
