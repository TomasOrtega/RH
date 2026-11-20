import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

/- English proof (translation)
Introduce `X U V j v hj hv ζ N hζ k _ y hN hy`. Use `set s : Γ(V, ⊤) := ∑ i ∈ Finset.range N, ζ ^ i with hs`. Establish `hmul : s * (ζ - 1) = 0` using `by rw [hs, geom_sum_mul, hζ, sub_self]`. Establish `hys : y.appTop.hom s = (N : Γ(Sp k, ⊤))`. Simplify using `[hs, map_sum, map_pow, hy]`.

Establish `hunit : IsUnit (y.appTop.hom s)`. Rewrite using `[hys]`. Establish `h1 : IsUnit (N : k)` using `isUnit_iff_ne_zero.mpr hN`. Establish `h2` using `h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hpre : y ⁻¹ᵁ V.basicOpen s = ⊤`. Rewrite using `[Scheme.preimage_basicOpen_top]`. Conclude with `(Sp k).basicOpen_of_isUnit hunit`. Establish `hne : ((V.basicOpen s : V.Opens) : Set V).Nonempty`. Take `⟨p⟩ : Nonempty (Sp k)` from `inferInstanceAs (Nonempty (PrimeSpectrum k))`.

Use `⟨y p, ?_⟩` and prove the remaining obligations. Establish `: p ∈ y ⁻¹ᵁ V.basicOpen s` using `by rw [hpre]; trivial`. Conclude with `this`. Establish `hopen : IsOpen (v '' ((V.basicOpen s : V.Opens) : Set V))` using `v.isOpenEmbedding.isOpenMap _ (V.basicOpen s).isOpen`. Take `⟨u₀, z₀, hz₀, hzu⟩` from `j.denseRange.exists_mem_open hopen (hne.image _)`.

Take `⟨w, hw1, hw2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := v) (g := j) z₀ u₀ hzu`. Set `P` to `pullback v j`. Set `K : Type` to `AlgebraicClosure (P.residueField w)`. Set `q : Sp K ⟶ P` to `spMap (algebraMap (P.residueField w) K) ≫ P.fromSpecResidueField w`. Establish `hq : ∀ p, q p = w`.

Introduce `p`. Simplify using `only [q, Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _`. Use `⟨K, inferInstance, inferInstance, q ≫ pullback.snd v j, q ≫ pullback.fst v j, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Category.assoc, pullback.condition]`.

Use `set z := q ≫ pullback.fst v j with hz`. Establish `hzs : z.appTop.hom s ≠ 0`. Introduce `h0`. Take `⟨p⟩ : Nonempty (Sp K)` from `inferInstanceAs (Nonempty (PrimeSpectrum K))`. Establish `hp : p ∈ z ⁻¹ᵁ V.basicOpen s`.

Express the relevant statement in the definitionally equal form `z p ∈ V.basicOpen s`. Rewrite using `[hz, Scheme.Hom.comp_apply, hq, hw1]`. Conclude with `hz₀`. Rewrite `hp` using `[Scheme.preimage_basicOpen_top]`. Establish `: (Sp K).basicOpen (z.appTop.hom s) = ⊥`.

Rewrite using `[h0]`. Conclude with `(Sp K).basicOpen_zero _`. Establish `hp' : p ∈ (Sp K).basicOpen (z.appTop.hom s)` using `hp`. Rewrite `hp'` using `[this]`. Conclude with `hp'`.

Use `haveI : IsDomain Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain`. Establish `h` using `congrArg z.appTop.hom hmul`. Rewrite `h` using `[map_mul, map_zero, map_sub, map_one]`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hzs)`.
-/
theorem exists_geometricPoint_rootOfUnity_eq_one_of_isDominant :
    ∀ (X U V : Scheme.{0}) (j : U ⟶ X) (v : V ⟶ X), IsDominant j → IsOpenImmersion v → ∀ (ζ : Γ(V, ⊤)) (N : ℕ), ζ ^ N = 1 → ∀ (k : Type) [Field k] (y : Sp k ⟶ V), (N : k) ≠ 0 → y.appTop.hom ζ = 1 → ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Sp K ⟶ U) (z : Sp K ⟶ V), z ≫ v = u ≫ j ∧ z.appTop.hom ζ = 1 := by
  intro X U V j v hj hv ζ N hζ k _ y hN hy
  classical
  set s : Γ(V, ⊤) := ∑ i ∈ Finset.range N, ζ ^ i with hs
  have hmul : s * (ζ - 1) = 0 := by rw [hs, geom_sum_mul, hζ, sub_self]
  have hys : y.appTop.hom s = (N : Γ(Sp k, ⊤)) := by
    simp [hs, map_sum, map_pow, hy]
  have hunit : IsUnit (y.appTop.hom s) := by
    rw [hys]
    have h1 : IsUnit (N : k) := isUnit_iff_ne_zero.mpr hN
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at h2
  have hpre : y ⁻¹ᵁ V.basicOpen s = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact (Sp k).basicOpen_of_isUnit hunit
  have hne : ((V.basicOpen s : V.Opens) : Set V).Nonempty := by
    obtain ⟨p⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    refine ⟨y p, ?_⟩
    have : p ∈ y ⁻¹ᵁ V.basicOpen s := by rw [hpre]; trivial
    exact this
  have hopen : IsOpen (v '' ((V.basicOpen s : V.Opens) : Set V)) :=
    v.isOpenEmbedding.isOpenMap _ (V.basicOpen s).isOpen
  obtain ⟨u₀, z₀, hz₀, hzu⟩ := j.denseRange.exists_mem_open hopen (hne.image _)
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := v) (g := j) z₀ u₀ hzu
  let P := pullback v j
  let K : Type := AlgebraicClosure (P.residueField w)
  let q : Sp K ⟶ P := spMap (algebraMap (P.residueField w) K) ≫ P.fromSpecResidueField w
  have hq : ∀ p, q p = w := by
    intro p
    simp only [q, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  refine ⟨K, inferInstance, inferInstance, q ≫ pullback.snd v j, q ≫ pullback.fst v j, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
  · set z := q ≫ pullback.fst v j with hz
    have hzs : z.appTop.hom s ≠ 0 := by
      intro h0
      obtain ⟨p⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
      have hp : p ∈ z ⁻¹ᵁ V.basicOpen s := by
        change z p ∈ V.basicOpen s
        rw [hz, Scheme.Hom.comp_apply, hq, hw1]
        exact hz₀
      rw [Scheme.preimage_basicOpen_top] at hp
      have : (Sp K).basicOpen (z.appTop.hom s) = ⊥ := by
        rw [h0]; exact (Sp K).basicOpen_zero _
      have hp' : p ∈ (Sp K).basicOpen (z.appTop.hom s) := hp
      rw [this] at hp'
      exact hp'
    haveI : IsDomain Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    have h := congrArg z.appTop.hom hmul
    rw [map_mul, map_zero, map_sub, map_one] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hzs)

end GlobalTheory
