import Mathlib
import Formalism.HermitianLattices.StatementLat

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Unfold `gmap`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.

Introduce `hx`. Conclude with `⟨g.symm x, hx, by simp⟩`.
-/
theorem isomAct_mem_gmap (g : V ≃ₗ[K] V) (L : Submodule R V) (x : V) :
    x ∈ gmap g L ↔ g.symm x ∈ L := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

/- English proof (translation)
Conclude with `map_smul ((g : V →ₗ[K] V).restrictScalars R) s x`.
-/
theorem isomAct_smul (g : V ≃ₗ[K] V) (s : R) (x : V) : g (s • x) = s • g x := by
  exact map_smul ((g : V →ₗ[K] V).restrictScalars R) s x

/- English proof (translation)
Use extensionality with `x`. Simplify using `[isomAct_mem_gmap]`.
-/
theorem isomAct_gmap_symm (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g.symm (gmap g L) = L := by
  ext x
  simp [isomAct_mem_gmap]

/- English proof (translation)
Simplify using `only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`.
-/
theorem isomAct_mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

/- English proof (translation)
Establish `e : ((gmap g L : Submodule R V) : Set V) = (g : V →ₗ[K] V) '' (L : Set V)`. Use extensionality with `x`. Simplify using `[gmap]`. Use `⟨hL.fg.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[e, Submodule.span_image, hL.span_eq_top, Submodule.map_top]`.

Conclude with `LinearEquiv.range g`.
-/
theorem isomAct_lattice (g : V ≃ₗ[K] V) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (gmap g L) := by
  have e : ((gmap g L : Submodule R V) : Set V) = (g : V →ₗ[K] V) '' (L : Set V) := by
    ext x
    simp [gmap]
  refine ⟨hL.fg.map _, ?_⟩
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top]
  exact LinearEquiv.range g

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isomAct_mem_locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R)
    (L : Submodule R W) (x : W) : x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := Iff.rfl

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ h g hg L`. Establish `iso : ∀ x y, h (g x) (g y) = h x y` using `hg`. Establish `hdual : dual h (gmap g L) = gmap g (dual h L)`. Use extensionality with `x`. Rewrite using `[isomAct_mem_gmap, isomAct_mem_dual, isomAct_mem_dual]`.

Prove the components needed by the constructor for the conclusion. Introduce `H z hz`. Establish `hz' : g z ∈ gmap g L`. Rewrite using `[isomAct_mem_gmap]`. Simplify using `using hz`.

Establish `e` using `H (g z) hz'`. Rewrite using `[← iso z (g.symm x)]`. Simplify using `using e`. Introduce `H y hy`. Rewrite `hy` using `[isomAct_mem_gmap]`.

Establish `e` using `H _ hy`. Rewrite `e` using `[← iso (g.symm y) (g.symm x)]`. Simplify using `using e`. Establish `hsat : ∀ S : Submonoid R, locS S (gmap g L) = gmap g (locS S L)`. Introduce `S`.

Use extensionality with `x`. Simplify using `only [isomAct_mem_gmap, isomAct_mem_locS, isomAct_smul]`. Establish `hint_r : IsIntegralLat h (gmap g L) ↔ IsIntegralLat h L`. Unfold `IsIntegralLat`. Prove the components needed by the constructor for the conclusion.

Introduce `H x hx y hy`. Establish `hx' : g x ∈ gmap g L`. Rewrite using `[isomAct_mem_gmap]`. Simplify using `using hx`. Establish `hy' : g y ∈ gmap g L`.

Rewrite using `[isomAct_mem_gmap]`. Simplify using `using hy`. Rewrite using `[← iso x y]`. Conclude with `H _ hx' _ hy'`. Introduce `H x hx y hy`.

Rewrite `hx`, `hy` using `[isomAct_mem_gmap]`. Establish `e` using `H _ hx _ hy`. Rewrite `e` using `[← iso (g.symm x) (g.symm y)]`. Simplify using `using e`. Establish `hunim : IsUnimodular h (gmap g L) ↔ IsUnimodular h L`.

Unfold `IsUnimodular`. Rewrite using `[hdual]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `e` using `congrArg (gmap (R := R) g.symm) H`.

Simplify using `only [isomAct_gmap_symm] at e`. Conclude with `e`. Introduce `H`. Rewrite using `[H]`. Establish `hlat : Submodule.IsLattice K (gmap g L) ↔ Submodule.IsLattice K L`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `e` using `isomAct_lattice g.symm (gmap g L) H`. Rewrite `e` using `[isomAct_gmap_symm]`. Then use the resulting hypothesis. Introduce `H`.

Conclude with `isomAct_lattice g L H`. Use `⟨hdual, ?_, hint_r, hunim, hlat⟩` and prove the remaining obligations. Introduce `p`. Unfold `loc`. Conclude with `hsat _`.
-/
theorem isomAct : IsomAct := by
  intro R K V _ _ _ _ _ _ _ _ h g hg L
  have iso : ∀ x y, h (g x) (g y) = h x y := hg
  have hdual : dual h (gmap g L) = gmap g (dual h L) := by
    ext x
    rw [isomAct_mem_gmap, isomAct_mem_dual, isomAct_mem_dual]
    constructor
    · intro H z hz
      have hz' : g z ∈ gmap g L := by
        rw [isomAct_mem_gmap]
        simpa using hz
      have e := H (g z) hz'
      rw [← iso z (g.symm x)]
      simpa using e
    · intro H y hy
      rw [isomAct_mem_gmap] at hy
      have e := H _ hy
      rw [← iso (g.symm y) (g.symm x)] at e
      simpa using e
  have hsat : ∀ S : Submonoid R, locS S (gmap g L) = gmap g (locS S L) := by
    intro S
    ext x
    simp only [isomAct_mem_gmap, isomAct_mem_locS, isomAct_smul]
  have hint_r : IsIntegralLat h (gmap g L) ↔ IsIntegralLat h L := by
    unfold IsIntegralLat
    constructor
    · intro H x hx y hy
      have hx' : g x ∈ gmap g L := by
        rw [isomAct_mem_gmap]
        simpa using hx
      have hy' : g y ∈ gmap g L := by
        rw [isomAct_mem_gmap]
        simpa using hy
      rw [← iso x y]
      exact H _ hx' _ hy'
    · intro H x hx y hy
      rw [isomAct_mem_gmap] at hx hy
      have e := H _ hx _ hy
      rw [← iso (g.symm x) (g.symm y)] at e
      simpa using e
  have hunim : IsUnimodular h (gmap g L) ↔ IsUnimodular h L := by
    unfold IsUnimodular
    rw [hdual]
    constructor
    · intro H
      have e := congrArg (gmap (R := R) g.symm) H
      simp only [isomAct_gmap_symm] at e
      exact e
    · intro H
      rw [H]
  have hlat : Submodule.IsLattice K (gmap g L) ↔ Submodule.IsLattice K L := by
    constructor
    · intro H
      have e := isomAct_lattice g.symm (gmap g L) H
      rwa [isomAct_gmap_symm] at e
    · intro H
      exact isomAct_lattice g L H
  refine ⟨hdual, ?_, hint_r, hunim, hlat⟩
  intro p
  unfold loc
  exact hsat _

end Formalism.HermitianLatticesTheory
