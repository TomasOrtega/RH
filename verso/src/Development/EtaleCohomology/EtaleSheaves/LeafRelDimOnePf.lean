import Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafRelDimOnePf

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `: Subsingleton C` using `⟨fun a b => (h a).trans (h b).symm⟩`. Establish `: DiscreteTopology C` using `inferInstance`. Use `topologicalKrullDim_zero_of_discreteTopology C` as an intermediate fact.

Rewrite `this` using `[hd]`. Conclude with `absurd this (by decide)`.
-/
theorem exists_ne_generic {C : Scheme.{0}} [IsIntegral C] (hd : topologicalKrullDim C = 1) :
    ∃ x : C, x ≠ genericPoint C := by
  by_contra h
  push Not at h
  have : Subsingleton C := ⟨fun a b => (h a).trans (h b).symm⟩
  have : DiscreteTopology C := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hd] at this
  exact absurd this (by decide)

/- English proof (translation)
The claim follows from `MulEquiv.isField (Field.toIsField Ω) (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv`.
-/
theorem isField_top (Ω : Type) [Field Ω] : IsField Γ(Sp Ω, ⊤) :=
  MulEquiv.isField (Field.toIsField Ω)
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv

/- English proof (translation)
Establish `hU : U = ⊤`. Use extensionality with `p`. Simplify using `only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]`. Establish `: p = c x` using `Subsingleton.elim _ _`. Substitute `this` using the available equality.

Conclude with `e hx`. Substitute `hU` using the available equality. Establish `: Nonempty V` using `⟨⟨x, hx⟩⟩`. Set `: Field Γ(Sp Ω, ⊤)` to `(isField_top Ω).toField`. Set `: Algebra Γ(Sp Ω, ⊤) Γ(C, V)` to `(c.appLE ⊤ V e).hom.toAlgebra`.

Take `⟨ι, σ, _, _, ⟨P⟩⟩` from `hs.out`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp Ω, ⊤) Γ(C, V)` using `P.isStandardSmoothOfRelativeDimension rfl`. Establish `h1` using `GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := Γ(Sp Ω, ⊤)) (A := Γ(C, V)) (d := P.dimension)`. Establish `hle : ringKrullDim Γ(C, V) ≤ 1`. Rewrite using `[← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]`.

Conclude with `hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le`. Establish `hne : ringKrullDim Γ(C, V) ≠ 0`. Introduce `h0`. Establish `: Ring.KrullDimLE 0 Γ(C, V)` using `Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)`. Establish `hF` using `Ring.KrullDimLE.isField_of_isDomain (R := Γ(C, V))`.

Set `` to `hF.toField`. Establish `hη : genericPoint C ∈ V` using `((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, by simp, hx⟩`. Establish `hx' : x ∈ Set.range hV.fromSpec` using `by rw [hV.range_fromSpec]; exact hx`. Establish `hη' : genericPoint C ∈ Set.range hV.fromSpec` using `by rw [hV.range_fromSpec]; exact hη`. Take `⟨a, rfl⟩` from `hx'`.

Take `⟨b, hb⟩` from `hη'`. Apply `hxη` to reduce the goal to its premises. Rewrite using `[← hb]`. Establish `key : ∀ p : PrimeSpectrum Γ(C, V), p.asIdeal = ⊥`. Introduce `p`.

Establish `hp` using `p.isPrime`. Conclude with `Ideal.eq_bot_of_prime _`. Use `congr 1`. Conclude with `PrimeSpectrum.ext ((key a).trans (key b).symm)`. Rewrite `hle`, `hne` using `[h1]`.

Establish `h2 : P.dimension ≤ 1` using `by exact_mod_cast hle`. Establish `h3 : P.dimension ≠ 0` using `by exact_mod_cast hne`. Conclude with `P.isStandardSmoothOfRelativeDimension (by omega)`.
-/
theorem chart (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [IsIntegral C]
    (hd : topologicalKrullDim C = 1) (U : (Sp Ω).Opens) (V : C.Opens) (hV : IsAffineOpen V)
    (x : C) (hx : x ∈ V) (hxη : x ≠ genericPoint C) (e : V ≤ c ⁻¹ᵁ U)
    (hs : (c.appLE U V e).hom.IsStandardSmooth) :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (c.appLE U V e).hom := by
  have hU : U = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : p = c x := Subsingleton.elim _ _
    subst this
    exact e hx
  subst hU
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let : Field Γ(Sp Ω, ⊤) := (isField_top Ω).toField
  let : Algebra Γ(Sp Ω, ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp Ω, ⊤) Γ(C, V) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have h1 := GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := Γ(Sp Ω, ⊤)) (A := Γ(C, V))
    (d := P.dimension)
  have hle : ringKrullDim Γ(C, V) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim Γ(C, V) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 Γ(C, V) := Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)
    have hF := Ring.KrullDimLE.isField_of_isDomain (R := Γ(C, V))
    let := hF.toField
    have hη : genericPoint C ∈ V :=
      ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, by simp, hx⟩
    have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
    have hη' : genericPoint C ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hη
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, hb⟩ := hη'
    apply hxη
    rw [← hb]
    have key : ∀ p : PrimeSpectrum Γ(C, V), p.asIdeal = ⊥ := by
      intro p
      have hp := p.isPrime
      exact Ideal.eq_bot_of_prime _
    congr 1
    exact PrimeSpectrum.ext ((key a).trans (key b).symm)
  rw [h1] at hle hne
  have h2 : P.dimension ≤ 1 := by exact_mod_cast hle
  have h3 : P.dimension ≠ 0 := by exact_mod_cast hne
  exact P.isStandardSmoothOfRelativeDimension (by omega)

/- English proof (translation)
Introduce `Ω _ C c hC hs hd`. Take `⟨x₀, hx₀⟩` from `exists_ne_generic hd`. Prove the components needed by the constructor for the conclusion. Introduce `y`. Distinguish the cases in `hy : y = genericPoint C`.

Take `⟨U, hU, V, hV, hx, e, h⟩` from `Smooth.exists_isStandardSmooth c x₀`. Establish `hyV : y ∈ V` using `hy ▸ ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x₀, by simp, hx⟩`. Conclude with `⟨U, hU, V, hV, hyV, e, chart Ω c hd U V hV x₀ hx hx₀ e h⟩`. Take `⟨U, hU, V, hV, hx, e, h⟩` from `Smooth.exists_isStandardSmooth c y`. Conclude with `⟨U, hU, V, hV, hx, e, chart Ω c hd U V hV y hx hy e h⟩`.
-/
theorem LeafRelDimOne_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := by
  intro Ω _ C c hC hs hd
  obtain ⟨x₀, hx₀⟩ := exists_ne_generic hd
  constructor
  intro y
  by_cases hy : y = genericPoint C
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c x₀
    have hyV : y ∈ V := hy ▸ ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x₀, by simp, hx⟩
    exact ⟨U, hU, V, hV, hyV, e, chart Ω c hd U V hV x₀ hx hx₀ e h⟩
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c y
    exact ⟨U, hU, V, hV, hx, e, chart Ω c hd U V hV y hx hy e h⟩

end LateralTheory.E.LeafRelDimOnePf
