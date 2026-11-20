import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
The claim follows from `spMap_inj ((cancel_mono hU.fromSpec).1 h)`.
-/
theorem chart_inj {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {B : Type} [CommRing B] {f g : Γ(X, U) →+* B}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g :=
  spMap_inj ((cancel_mono hU.fromSpec).1 h)

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMapR]`.
-/
theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMapR (g.comp f) = (dualMapR g).comp (dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMapR]

/- English proof (translation)
Set `p : PrimeSpectrum S` to `PrimeSpectrum.comap ψ (IsLocalRing.closedPoint K)`. Set `W : TopologicalSpace.Opens (PrimeSpectrum S)` to `x ⁻¹ᵁ U`. Establish `hp : p ∈ (W : Set (PrimeSpectrum S))`. Establish `e : x p = hU.fromSpec (spMap f (IsLocalRing.closedPoint K))`. Use `congrArg (fun q : Sp K ⟶ X => q (IsLocalRing.closedPoint K)) hf` as an intermediate fact.

Conclude with `this`. Use `show x p ∈ (U : Set X)`. Rewrite using `[e, ← hU.range_fromSpec]`. Conclude with `⟨_, rfl⟩`. Take `⟨_, ⟨h, rfl⟩, h1, h2⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen`.

Use `⟨h, fun h0 => h1 ?_, ?_⟩` and prove the remaining obligations. Use `show ψ h ∈ (IsLocalRing.closedPoint K).asIdeal`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Establish `hr : Set.range (spMap (algebraMap S (Localization.Away h)) ≫ x) ⊆ Set.range hU.fromSpec`.

Rewrite using `[hU.range_fromSpec]`. Introduce and unpack `_ ⟨q, rfl⟩`. Use `h2 (a := PrimeSpectrum.comap (algebraMap S (Localization.Away h)) q) fun hq => ?_` and prove the remaining obligations. Conclude with `q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq (IsLocalization.Away.algebraMap_isUnit h))`. Set `g` to `IsOpenImmersion.lift hU.fromSpec _ hr`.

Establish `hg : g ≫ hU.fromSpec = _` using `IsOpenImmersion.lift_fac _ _ _`. Establish `e : spMap (Spec.preimage g).hom = g` using `Spec.map_preimage g`. Conclude with `⟨(Spec.preimage g).hom, by rw [e]; exact hg.symm⟩`.
-/
theorem exists_spread {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {S K : Type} [CommRing S] [Field K]
    (x : Sp S ⟶ X) (ψ : S →+* K) (f : Γ(X, U) →+* K) (hf : spMap ψ ≫ x = spMap f ≫ hU.fromSpec) :
    ∃ h : S, ψ h ≠ 0 ∧ ∃ fh : Γ(X, U) →+* Localization.Away h,
      spMap (algebraMap S (Localization.Away h)) ≫ x = spMap fh ≫ hU.fromSpec := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap ψ (IsLocalRing.closedPoint K)
  let W : TopologicalSpace.Opens (PrimeSpectrum S) := x ⁻¹ᵁ U
  have hp : p ∈ (W : Set (PrimeSpectrum S)) := by
    have e : x p = hU.fromSpec (spMap f (IsLocalRing.closedPoint K)) := by
      have := congrArg (fun q : Sp K ⟶ X => q (IsLocalRing.closedPoint K)) hf
      exact this
    show x p ∈ (U : Set X)
    rw [e, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨_, ⟨h, rfl⟩, h1, h2⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp
    W.isOpen
  refine ⟨h, fun h0 => h1 ?_, ?_⟩
  · show ψ h ∈ (IsLocalRing.closedPoint K).asIdeal
    rw [h0]
    exact zero_mem _
  have hr : Set.range (spMap (algebraMap S (Localization.Away h)) ≫ x) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    refine h2 (a := PrimeSpectrum.comap (algebraMap S (Localization.Away h)) q) fun hq => ?_
    exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq (IsLocalization.Away.algebraMap_isUnit h))
  let g := IsOpenImmersion.lift hU.fromSpec _ hr
  have hg : g ≫ hU.fromSpec = _ := IsOpenImmersion.lift_fac _ _ _
  have e : spMap (Spec.preimage g).hom = g := Spec.map_preimage g
  exact ⟨(Spec.preimage g).hom, by rw [e]; exact hg.symm⟩

/- English proof (translation)
Use `letI := α.toAlgebra`. Take `⟨s, hs⟩` from `Algebra.FiniteType.out (R := O) (A := A) (self := h)`. Use `⟨s, fun Q h1 h2 a => ?_⟩` and prove the remaining obligations. Establish `ha : a ∈ Algebra.adjoin O (s : Set A)` using `hs ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`.

Consider the case `mem a ha => exact h2 a ha`. Consider the case `algebraMap o => exact h1 o`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`.
-/
theorem fin_gen {O A : Type} [CommRing O] [CommRing A] {α : O →+* A} (h : α.FiniteType) :
    ∃ s : Finset A, ∀ Q : Subring A, (∀ o, α o ∈ Q) → (∀ a ∈ s, a ∈ Q) → ∀ a, a ∈ Q := by
  letI := α.toAlgebra
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := O) (A := A) (self := h)
  refine ⟨s, fun Q h1 h2 a => ?_⟩
  have ha : a ∈ Algebra.adjoin O (s : Set A) := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact h2 a ha
  | algebraMap o => exact h1 o
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

end ModelDimension.Near
