import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.GmapLocEqOfFrame

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `hpos` using `isTotPosDef_of_ortho hK hs hI`. Establish `hd : ∀ x, h x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`.

Use `hpos x hne φ` as an intermediate fact. Rewrite `this` using `[hx, map_zero]`. Simplify using `at this`. Take `⟨e, -, hspan, rfl, he⟩` from `hI`. Take `⟨g, hg, hge⟩` from `WA.exists_isom_frame (WA.isHermSemilocal_locRing hK hp) hs hd (WA.isSelfDualMod_loc hL hp.isPrime hu) e he`.

Conclude with `⟨g, hg, WA.gmap_loc_eq_of_frame hp.isPrime hu hspan he hg hge⟩`.
-/
theorem exists_isom_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (p : Ideal (𝓞 K)) (hp : p.IsMaximal)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p I) = Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hpos := isTotPosDef_of_ortho hK hs hI
  have hd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hne φ
    rw [hx, map_zero] at this
    simp at this
  obtain ⟨e, -, hspan, rfl, he⟩ := hI
  obtain ⟨g, hg, hge⟩ := WA.exists_isom_frame (WA.isHermSemilocal_locRing hK hp) hs hd
    (WA.isSelfDualMod_loc hL hp.isPrime hu) e he
  exact ⟨g, hg, WA.gmap_loc_eq_of_frame hp.isPrime hu hspan he hg hge⟩

end ReciprocityTheory.ChartRestriction.L3
