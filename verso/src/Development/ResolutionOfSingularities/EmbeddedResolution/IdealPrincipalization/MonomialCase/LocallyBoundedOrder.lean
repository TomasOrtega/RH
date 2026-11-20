import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `x hx`. Establish `hx' : stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))` using `hx`. Choose the witnesses or unpack the hypotheses as in `⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by`. Establish `h1 : x ∈ (⨆ i : X.affineOpens, (i : X.Opens))`.

Rewrite using `[AlgebraicGeometry.iSup_affineOpens_eq_top X]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.mp h1`. Establish `: IsNoetherianRing Γ(X, (U : X.Opens))` using `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U`. Take `⟨s, hs⟩ : (J.ideal U).FG` from `IsNoetherian.noetherian (J.ideal U)`.

Establish `hzero : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) x hxU).hom g = 0`. Introduce `g hg`. Establish `hgI : g ∈ J.ideal U`. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span (Finset.mem_coe.mpr hg)`.

Establish `hmem` using `germ_mem_stalkIdeal J x U hxU hgI`. Rewrite `hmem` using `[hx']`. Simplify using `using hmem`. Establish `hWex : ∀ g : Γ(X, (U : X.Opens)), ∃ (W : X.Opens) (i : W ⟶ (U : X.Opens)), x ∈ W ∧ (g ∈ s → (X.presheaf.map i.op).hom g = 0)`. Introduce `g`.

Distinguish the cases in `hg : g ∈ s`. Take `⟨V, iV, hxV, hi⟩` from `X.toLocallyRingedSpace.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero (U : X.Opens) g ⟨x, hxU⟩ (hzero g hg)`. Conclude with `⟨V, iV, hxV, fun _ => hi⟩`. Conclude with `⟨(U : X.Opens), 𝟙 _, hxU, fun h => absurd h hg⟩`. Use `choose W i hxW hres using hWex`.

Use `⟨((U : X.Opens) : Set ↥X) ∩ ⋂ g ∈ (s : Set Γ(X, (U : X.Opens))), ((W g : X.Opens) : Set ↥X), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hyU, hyW⟩`. Establish `hyW' : ∀ g ∈ s, y ∈ W g` using `fun g hg => Set.mem_iInter₂.mp hyW g (Finset.mem_coe.mpr hg)`. Establish `hmain : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) y hyU).hom g = 0`. Introduce `g hg`.

Establish `h3 : (X.presheaf.germ (W g) y (hyW' g hg)).hom ((X.presheaf.map (i g).op).hom g) = 0`. Rewrite using `[hres g hg, map_zero]`. Conclude with `(X.presheaf.germ_res_apply (i g) y (hyW' g hg) g).symm.trans h3`. Use `show stalkIdeal J y = ⊥`. Rewrite using `[stalkIdeal_eq_map_germ J y U hyU, ← le_bot_iff, Ideal.map_le_iff_le_comap, ← hs, Submodule.span_le]`.

Introduce `g hg`. Establish `hg0` using `hmain g (Finset.mem_coe.mp hg)`. Establish `hmem : (X.presheaf.germ (U : X.Opens) y hyU).hom g ∈ (⊥ : Ideal (X.presheaf.stalk y))`. Rewrite using `[hg0]`. Conclude with `Submodule.zero_mem _`.

Simplify using `using hmem`. Conclude with `(TopologicalSpace.Opens.isOpen (U : X.Opens)).inter (Set.Finite.isOpen_biInter s.finite_toSet (fun g _ => TopologicalSpace.Opens.isOpen (W g)))`. Conclude with `⟨hxU, Set.mem_iInter₂.mpr (fun g _ => hxW g)⟩`.
-/
theorem isOpen_setOf_stalkIdeal_eq_bot {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (J : X.IdealSheafData) :
    IsOpen {x : ↥X | stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x)) := hx
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    have h1 : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  obtain ⟨s, hs⟩ : (J.ideal U).FG := IsNoetherian.noetherian (J.ideal U)
  have hzero : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) x hxU).hom g = 0 := by
    intro g hg
    have hgI : g ∈ J.ideal U := by
      rw [← hs]
      exact Submodule.subset_span (Finset.mem_coe.mpr hg)
    have hmem := germ_mem_stalkIdeal J x U hxU hgI
    rw [hx'] at hmem
    simpa using hmem
  have hWex : ∀ g : Γ(X, (U : X.Opens)), ∃ (W : X.Opens) (i : W ⟶ (U : X.Opens)),
      x ∈ W ∧ (g ∈ s → (X.presheaf.map i.op).hom g = 0) := by
    intro g
    by_cases hg : g ∈ s
    · obtain ⟨V, iV, hxV, hi⟩ :=
        X.toLocallyRingedSpace.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero
          (U : X.Opens) g ⟨x, hxU⟩ (hzero g hg)
      exact ⟨V, iV, hxV, fun _ => hi⟩
    · exact ⟨(U : X.Opens), 𝟙 _, hxU, fun h => absurd h hg⟩
  choose W i hxW hres using hWex
  refine ⟨((U : X.Opens) : Set ↥X) ∩
      ⋂ g ∈ (s : Set Γ(X, (U : X.Opens))), ((W g : X.Opens) : Set ↥X), ?_, ?_, ?_⟩
  · rintro y ⟨hyU, hyW⟩
    have hyW' : ∀ g ∈ s, y ∈ W g := fun g hg =>
      Set.mem_iInter₂.mp hyW g (Finset.mem_coe.mpr hg)
    have hmain : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) y hyU).hom g = 0 := by
      intro g hg
      have h3 : (X.presheaf.germ (W g) y (hyW' g hg)).hom
          ((X.presheaf.map (i g).op).hom g) = 0 := by
        rw [hres g hg, map_zero]
      exact (X.presheaf.germ_res_apply (i g) y (hyW' g hg) g).symm.trans h3
    show stalkIdeal J y = ⊥
    rw [stalkIdeal_eq_map_germ J y U hyU, ← le_bot_iff, Ideal.map_le_iff_le_comap, ← hs,
      Submodule.span_le]
    intro g hg
    have hg0 := hmain g (Finset.mem_coe.mp hg)
    have hmem : (X.presheaf.germ (U : X.Opens) y hyU).hom g ∈
        (⊥ : Ideal (X.presheaf.stalk y)) := by
      rw [hg0]
      exact Submodule.zero_mem _
    simpa using hmem
  · exact (TopologicalSpace.Opens.isOpen (U : X.Opens)).inter
      (Set.Finite.isOpen_biInter s.finite_toSet
        (fun g _ => TopologicalSpace.Opens.isOpen (W g)))
  · exact ⟨hxU, Set.mem_iInter₂.mpr (fun g _ => hxW g)⟩

/- English proof (translation)
Use `hT.locallyOfFiniteType` as an intermediate fact. Establish `: IsNoetherianRing T.base` using `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `U`. Conclude with `@isNoetherianRing_sections T.base _ _ T.scheme T.structMap _ U (sectionsAlgebra T.base T.structMap U.1) (algebraMap_sectionsAlgebra T.base T.structMap U.1)`.
-/
private theorem isLocallyNoetherian_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) :
    AlgebraicGeometry.IsLocallyNoetherian T.scheme := by
  have := hT.locallyOfFiniteType
  have : IsNoetherianRing T.base := inferInstance
  constructor
  intro U
  exact @isNoetherianRing_sections T.base _ _ T.scheme T.structMap _ U
    (sectionsAlgebra T.base T.structMap U.1)
    (algebraMap_sectionsAlgebra T.base T.structMap U.1)

/- English proof (translation)
Use `isLocallyNoetherian_of_isAdmissible T hT` as an intermediate fact. Introduce `hbot`. Take `⟨y, hyC, hyJ⟩` from `Set.not_subset.mp (hJ (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x))`. Establish `hirr : IsIrreducible (irreducibleComponent x)` using `isIrreducible_irreducibleComponent`. Establish `hcl : IsClosed ((J.support : Set ↥T.scheme))` using `J.support.2`.

Take `⟨z, hzC, hz1, hz2⟩` from `hirr.2 {w : ↥T.scheme | stalkIdeal J w = ⊥} ((J.support : Set ↥T.scheme)ᶜ) (isOpen_setOf_stalkIdeal_eq_bot J) hcl.isOpen_compl ⟨x, mem_irreducibleComponent, hbot⟩ ⟨y, hyC, hyJ⟩`. Establish `hz1' : stalkIdeal J z = ⊥` using `hz1`. Establish `hztop : stalkIdeal J z = ⊤`. Assume the negation of the conclusion as `hne`. Conclude with `hz2 ((mem_support_iff_stalkIdeal_ne_top J z).2 hne)`.

Establish `h1 : (1 : T.scheme.presheaf.stalk z) ∈ (⊥ : Ideal (T.scheme.presheaf.stalk z))`. Rewrite using `[← hz1', hztop]`. Conclude with `Submodule.mem_top`. Rewrite `h1` using `[Ideal.mem_bot]`. Conclude with `one_ne_zero h1`.
-/
private theorem stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) (x : ↥T.scheme) :
    stalkIdeal J x ≠ ⊥ := by
  have := isLocallyNoetherian_of_isAdmissible T hT
  intro hbot
  obtain ⟨y, hyC, hyJ⟩ := Set.not_subset.mp
    (hJ (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x))
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed ((J.support : Set ↥T.scheme)) := J.support.2
  obtain ⟨z, hzC, hz1, hz2⟩ :=
    hirr.2 {w : ↥T.scheme | stalkIdeal J w = ⊥} ((J.support : Set ↥T.scheme)ᶜ)
      (isOpen_setOf_stalkIdeal_eq_bot J) hcl.isOpen_compl
      ⟨x, mem_irreducibleComponent, hbot⟩ ⟨y, hyC, hyJ⟩
  have hz1' : stalkIdeal J z = ⊥ := hz1
  have hztop : stalkIdeal J z = ⊤ := by
    by_contra hne
    exact hz2 ((mem_support_iff_stalkIdeal_ne_top J z).2 hne)
  have h1 : (1 : T.scheme.presheaf.stalk z) ∈ (⊥ : Ideal (T.scheme.presheaf.stalk z)) := by
    rw [← hz1', hztop]
    exact Submodule.mem_top
  rw [Ideal.mem_bot] at h1
  exact one_ne_zero h1

/- English proof (translation)
Use `hT.charZero` as an intermediate fact. Use `hT.smooth` as an intermediate fact. Use `hT.locallyOfFiniteType` as an intermediate fact. Use `isLocallyNoetherian_of_isAdmissible T hT` as an intermediate fact. Establish `hfin : ∀ x : ↥T.scheme, orderAt J x ≠ ⊤` using `fun x => orderAt_ne_top_of_stalkIdeal_ne_bot J x (stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents T hT J hJ x)`.

Establish `hclosed : ∀ m : ℕ, IsClosed (orderAtLeastLocus J m)` using `fun m => isClosed_orderAtLeastLocus T.base T.structMap J m`. Establish `hspec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of T.base)))`. Simplify using the standard rewrite rules. Establish `hcpt : IsCompact (Set.univ : Set ↥T.scheme)`. Establish `h` using `hT.quasiCompact.isCompact_preimage Set.univ isOpen_univ hspec`.

Simplify using `using h`. Establish `hempty : (Set.univ : Set ↥T.scheme) ∩ (⋂ m : ℕ, orderAtLeastLocus J m) = ∅`. Rewrite using `[← Set.not_nonempty_iff_eq_empty]`. Introduce and unpack `⟨x, -, hx⟩`. Establish `hx'` using `Set.mem_iInter.mp hx`.

Establish `h1 : ∀ m : ℕ, (m : ℕ∞) ≤ orderAt J x` using `fun m => (mem_orderAtLeastLocus_iff J m x).1 (hx' m)`. Take `⟨n, hn⟩ : ∃ n : ℕ, orderAt J x = (n : ℕ∞)` from `⟨(orderAt J x).toNat, (ENat.natCast_toNat (hfin x)).symm⟩`. Establish `h3 : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞)`. Rewrite using `[← hn]`. Conclude with `h1 (n + 1)`.

Establish `h4 : n + 1 ≤ n` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu⟩` from `hcpt.elim_finite_subfamily_closed (fun m : ℕ => orderAtLeastLocus J m) hclosed hempty`. Establish `hMempty : ¬ ((Set.univ : Set ↥T.scheme) ∩ ⋂ i ∈ u, orderAtLeastLocus J i).Nonempty`. Rewrite using `[Set.not_nonempty_iff_eq_empty]`.

Conclude with `hu`. Use `⟨u.sup id, fun x => ?_⟩` and prove the remaining obligations. Establish `hxnot : x ∉ orderAtLeastLocus J (u.sup id)`. Introduce `hx`. Use `hMempty ⟨x, Set.mem_univ x, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_iInter]`. Introduce `i hi`. Conclude with `orderAtLeastLocus_subset_of_le J (Finset.le_sup (f := id) hi) hx`. Rewrite `hxnot` using `[mem_orderAtLeastLocus_iff]`. Conclude with `le_of_lt (not_le.mp hxnot)`.
-/
theorem exists_orderAt_le (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) :
    ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt J x ≤ (B : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  have := hT.locallyOfFiniteType
  have := isLocallyNoetherian_of_isAdmissible T hT
  have hfin : ∀ x : ↥T.scheme, orderAt J x ≠ ⊤ := fun x =>
    orderAt_ne_top_of_stalkIdeal_ne_bot J x
      (stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents T hT J hJ x)
  have hclosed : ∀ m : ℕ, IsClosed (orderAtLeastLocus J m) := fun m =>
    isClosed_orderAtLeastLocus T.base T.structMap J m
  have hspec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of T.base))) := by
    simp
  have hcpt : IsCompact (Set.univ : Set ↥T.scheme) := by
    have h := hT.quasiCompact.isCompact_preimage Set.univ isOpen_univ hspec
    simpa using h
  have hempty : (Set.univ : Set ↥T.scheme) ∩ (⋂ m : ℕ, orderAtLeastLocus J m) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hx⟩
    have hx' := Set.mem_iInter.mp hx
    have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ orderAt J x := fun m => (mem_orderAtLeastLocus_iff J m x).1 (hx' m)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, orderAt J x = (n : ℕ∞) :=
      ⟨(orderAt J x).toNat, (ENat.natCast_toNat (hfin x)).symm⟩
    have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      rw [← hn]
      exact h1 (n + 1)
    have h4 : n + 1 ≤ n := by exact_mod_cast h3
    omega
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed (fun m : ℕ => orderAtLeastLocus J m) hclosed hempty
  have hMempty : ¬ ((Set.univ : Set ↥T.scheme) ∩ ⋂ i ∈ u, orderAtLeastLocus J i).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty]
    exact hu
  refine ⟨u.sup id, fun x => ?_⟩
  have hxnot : x ∉ orderAtLeastLocus J (u.sup id) := by
    intro hx
    refine hMempty ⟨x, Set.mem_univ x, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact orderAtLeastLocus_subset_of_le J (Finset.le_sup (f := id) hi) hx
  rw [mem_orderAtLeastLocus_iff] at hxnot
  exact le_of_lt (not_le.mp hxnot)

end FunctorialResolution.EmbeddedResolution
