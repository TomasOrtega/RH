import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalClosed

open GlobalTheory.ThickeningClosed

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hZ : IsClosed (f '' Wᶜ)` using `f.isClosedMap _ hW.isClosed_compl`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal (f x).asIdeal (f x).isPrime.ne_top`. Set `p : PrimeSpectrum (CommRingCat.of R)` to `⟨m, hm.isPrime⟩`. Establish `h1 : p ∈ closure ({f x} : Set (PrimeSpectrum (CommRingCat.of R)))` using `(PrimeSpectrum.le_iff_mem_closure (f x) p).1 hle`.

Establish `hfx : f x ∈ f '' Wᶜ` using `⟨x, hx, rfl⟩`. Establish `hp : p ∈ f '' Wᶜ` using `closure_minimal (Set.singleton_subset_iff.2 hfx) hZ h1`. Take `⟨z, hz, hzp⟩` from `hp`. Apply `hz` to reduce the goal to its premises. Apply `h z` to reduce the goal to its premises.

Rewrite using `[hzp]`. Use `show I ≤ m`. Use `hI.trans ?_` and prove the remaining obligations. Unfold `Ideal.jacobson`. Conclude with `sInf_le ⟨bot_le, hm⟩`.
-/
theorem mem_of_forall_mem_over_closedFibre {R : Type} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {W : Set X} (hW : IsOpen W)
    (h : ∀ x, I ≤ (f x).asIdeal → x ∈ W) (x : X) : x ∈ W := by
  by_contra hx
  have hZ : IsClosed (f '' Wᶜ) := f.isClosedMap _ hW.isClosed_compl
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (f x).asIdeal (f x).isPrime.ne_top
  let p : PrimeSpectrum (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have h1 : p ∈ closure ({f x} : Set (PrimeSpectrum (CommRingCat.of R))) :=
    (PrimeSpectrum.le_iff_mem_closure (f x) p).1 hle
  have hfx : f x ∈ f '' Wᶜ := ⟨x, hx, rfl⟩
  have hp : p ∈ f '' Wᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hfx) hZ h1
  obtain ⟨z, hz, hzp⟩ := hp
  apply hz
  apply h z
  rw [hzp]
  show I ≤ m
  refine hI.trans ?_
  unfold Ideal.jacobson
  exact sInf_le ⟨bot_le, hm⟩

/- English proof (translation)
Apply `Scheme.IdealSheafData.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`. Rewrite using `[Scheme.IdealSheafData.ideal_bot]`. Apply `le_antisymm _ bot_le` to reduce the goal to its premises. Introduce `a ha`.

Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `ha0`. Set `J : Ideal Γ(X, U)` to `LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(X, U) a)`. Establish `hJ : J ≠ ⊤`. Introduce `hJ`.

Apply `ha0` to reduce the goal to its premises. Establish `h1 : (1 : Γ(X, U)) ∈ J` using `by rw [hJ]; exact Submodule.mem_top`. Simplify `h1` using `[J]`. Take `⟨m, hm, hJm⟩` from `Ideal.exists_le_maximal J hJ`. Take `⟨s, hs, hsa⟩` from `exists_mul_eq_zero_of_mem K U ⟨m, hm.isPrime⟩ (h _) ha`.

Apply `hs` to reduce the goal to its premises. Apply `hJm` to reduce the goal to its premises. Simplify `hsa` using `[J]`.
-/
theorem eq_bot_of_forall_mem_zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData)
    (h : ∀ x, x ∈ zeroLocusOpen K) : K = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_bot]
  apply le_antisymm _ bot_le
  intro a ha
  rw [Ideal.mem_bot]
  by_contra ha0
  let J : Ideal Γ(X, U) := LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(X, U) a)
  have hJ : J ≠ ⊤ := by
    intro hJ
    apply ha0
    have h1 : (1 : Γ(X, U)) ∈ J := by rw [hJ]; exact Submodule.mem_top
    simpa [J] using h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem K U ⟨m, hm.isPrime⟩ (h _) ha
  apply hs
  apply hJm
  simpa [J] using hsa

/- English proof (translation)
Introduce `R _ _ I hI X hX E j hj hth`. Use `haveI := hX`. Use `haveI := hj`. Use `haveI := hI`. Use `haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom`.

Rewrite using `[IsClosedImmersion.isIso_iff_ker_eq_bot]`. Apply `eq_bot_of_forall_mem_zeroLocusOpen` to reduce the goal to its premises. Introduce `x`. Use `mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom (isOpen_zeroLocusOpen _) ?_ x` and prove the remaining obligations. Introduce `y hy`.

Use `mem_of_thickenings I X.hom j ?_ y hy` and prove the remaining obligations. Introduce `n`. Take `⟨l, hl⟩` from `hth n`. Conclude with `⟨l, hl⟩`.
-/
theorem isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
    ∀ (E : Scheme.{0}) (j : E ⟶ X.left), IsClosedImmersion j →
      (∀ e, ∃ h : (thickObj R I e X).left ⟶ E, h ≫ j = pullback.fst X.hom (thick R I e)) →
        IsIso j := by
  intro R _ _ I hI X hX E j hj hth
  haveI := hX
  haveI := hj
  haveI := hI
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  apply eq_bot_of_forall_mem_zeroLocusOpen
  intro x
  refine mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
    (isOpen_zeroLocusOpen _) ?_ x
  intro y hy
  refine mem_of_thickenings I X.hom j ?_ y hy
  intro n
  obtain ⟨l, hl⟩ := hth n
  exact ⟨l, hl⟩

end GlobalTheory.CompanionTheory.FormalClosed
