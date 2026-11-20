import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordLoc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `h` using `TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2`. Establish `h2` using `congrArg (fun g => g.hom f) h`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h2`. Use `show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom ((X.presheaf.germ U q.1 hq).hom f)) = _`. Rewrite using `[h2]`.
-/
theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hξ : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hξ).hom f) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have h2 := congrArg (fun g => g.hom f) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom
    ((X.presheaf.germ U q.1 hq).hom f)) = _
  rw [h2]

end GlobalTheory.CompanionTheory.Ar.CoordLoc

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `X Ω _ ξ o _ _ κ x hT c p hp a`. Establish `hc : x c ≠ 0` using `hp.1`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Take `⟨U, hU, hUmem⟩` from `hT.affine c hc`.

Establish `hpU : p.1 ∈ U` using `(hUmem p.1).2 ⟨p.2, hp⟩`. Establish `hgU : genPt ξ ∈ U` using `p.2.mem_open U.isOpen hpU`. Set `φ : Γ(X, U) → Ω` to `fun f => (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hgU).hom f)`. Establish `hφA : ∀ f, φ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c)`. Introduce `f`.

Rewrite using `[hT.ring c hc]`. Introduce `q hq`. Establish `hqU : q.1 ∈ U` using `(hUmem q.1).2 ⟨q.2, hq⟩`. Conclude with `RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom f, CoordLoc.genMap_germ ξ U hgU q hqU f⟩`. Establish `hφp : ∀ f, φ f = genMap ξ p ((X.presheaf.germ U p.1 hpU).hom f)` using `fun f => (CoordLoc.genMap_germ ξ U hgU p hpU f).symm`.

Establish `ha' : a ∈ (genMap ξ p).range` using `ha`. Take `⟨g, rfl⟩` from `RingHom.mem_range.mp ha'`. Set `xU : U` to `⟨p.1, hpU⟩`. Use `hU.isLocalization_stalk xU` as an intermediate fact. Establish `hgerm : ∀ f, algebraMap Γ(X, U) (X.presheaf.stalk xU.1) f = (X.presheaf.germ U p.1 hpU).hom f` using `fun f => rfl`.

Take `⟨⟨t, s⟩, hts⟩` from `IsLocalization.mk'_surjective (hU.primeIdealOf xU).asIdeal.primeCompl (S := X.presheaf.stalk xU.1) g`. Establish `hspec` using `IsLocalization.mk'_spec (X.presheaf.stalk xU.1) t s`. Simplify using `only at hts`. Rewrite `hspec` using `[hts, hgerm, hgerm]`. Establish `hunit` using `IsLocalization.map_units (X.presheaf.stalk xU.1) s`.

Rewrite `hunit` using `[hgerm]`. Take `⟨u, hu⟩` from `hunit`. Use `⟨φ s, hφA s, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφp, ← hu]`. Conclude with `(u.isUnit.map (genMap ξ p)).ne_zero`.

Conclude with `⟨(X.presheaf.germ U p.1 hpU).hom s, (hφp s).symm⟩`. Use `RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩` and prove the remaining obligations. Rewrite using `[hφp, ← hu]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Establish `hmul : φ s * genMap ξ p g = φ t`. Rewrite using `[hφp, hφp, ← map_mul, mul_comm, hspec]`. Rewrite using `[hmul]`. Conclude with `hφA t`. Introduce and unpack `⟨s, _, ⟨hs0, _, hsinv⟩, hsa⟩`.

Establish `hsa' : s * a ∈ regAt ξ p` using `(hT.ring c hc (s * a)).mp hsa p hp`. Establish `heq : a = s⁻¹ * (s * a)`. Rewrite using `[← _root_.mul_assoc, inv_mul_cancel₀ hs0, _root_.one_mul]`. Rewrite using `[heq]`. Conclude with `Subring.mul_mem _ hsinv hsa'`.
-/
theorem regAt_iff_exists_chart_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  intro X Ω _ ξ o _ _ κ x hT c p hp a
  have hc : x c ≠ 0 := hp.1
  constructor
  · intro ha
    obtain ⟨U, hU, hUmem⟩ := hT.affine c hc
    have hpU : p.1 ∈ U := (hUmem p.1).2 ⟨p.2, hp⟩
    have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
    let φ : Γ(X, U) → Ω := fun f =>
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hgU).hom f)
    have hφA : ∀ f, φ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
      intro f
      rw [hT.ring c hc]
      intro q hq
      have hqU : q.1 ∈ U := (hUmem q.1).2 ⟨q.2, hq⟩
      exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom f, CoordLoc.genMap_germ ξ U hgU q hqU f⟩
    have hφp : ∀ f, φ f = genMap ξ p ((X.presheaf.germ U p.1 hpU).hom f) := fun f =>
      (CoordLoc.genMap_germ ξ U hgU p hpU f).symm
    have ha' : a ∈ (genMap ξ p).range := ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha'
    let xU : U := ⟨p.1, hpU⟩
    have := hU.isLocalization_stalk xU
    have hgerm : ∀ f, algebraMap Γ(X, U) (X.presheaf.stalk xU.1) f = (X.presheaf.germ U p.1 hpU).hom f :=
      fun f => rfl
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf xU).asIdeal.primeCompl
      (S := X.presheaf.stalk xU.1) g
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk xU.1) t s
    simp only at hts
    rw [hts, hgerm, hgerm] at hspec
    have hunit := IsLocalization.map_units (X.presheaf.stalk xU.1) s
    rw [hgerm] at hunit
    obtain ⟨u, hu⟩ := hunit
    refine ⟨φ s, hφA s, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hφp, ← hu]
      exact (u.isUnit.map (genMap ξ p)).ne_zero
    · exact ⟨(X.presheaf.germ U p.1 hpU).hom s, (hφp s).symm⟩
    · refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩
      rw [hφp, ← hu]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    · have hmul : φ s * genMap ξ p g = φ t := by
        rw [hφp, hφp, ← map_mul, mul_comm, hspec]
      rw [hmul]
      exact hφA t
  · rintro ⟨s, _, ⟨hs0, _, hsinv⟩, hsa⟩
    have hsa' : s * a ∈ regAt ξ p := (hT.ring c hc (s * a)).mp hsa p hp
    have heq : a = s⁻¹ * (s * a) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hs0, _root_.one_mul]
    rw [heq]
    exact Subring.mul_mem _ hsinv hsa'

end GlobalTheory.CompanionTheory.Ar
