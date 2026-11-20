import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A D hD`. Establish `hDF : (D : F) ≠ 0` using `Int.cast_ne_zero.2 hD`. Use `(HeightOneSpectrum.Support.finite (𝓞 F) ((D : F)⁻¹)).subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hs`. Apply `hp` to reduce the goal to its premises.

Establish `hs' : p.valuation F ((D : F)⁻¹) ≤ 1`. Use `hs` as an intermediate fact. Simplify using `only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at this`. Conclude with `this`. Establish `h1 : p.valuation F (D : F) ≤ 1`.

Use `p.valuation_le_one (K := F) (D : 𝓞 F)` as an intermediate fact. Simplify using `using this`. Establish `m1` using `((integers_local A).2.2.1 (D : F) p).2 h1`. Establish `m2` using `((integers_local A).2.2.1 ((D : F)⁻¹) p).2 hs'`. Establish `hne : (A.loc p).ιF (D : F) ≠ 0`.

Rewrite using `[map_ne_zero]`. Conclude with `hDF`. Use `⟨⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(A.loc p).ιF (D : F) * (A.loc p).ιF ((D : F)⁻¹) = 1`.

Rewrite using `[← map_mul, mul_inv_cancel₀ hDF, map_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(A.loc p).ιF ((D : F)⁻¹) * (A.loc p).ιF (D : F) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hDF, map_one]`. Express the relevant statement in the definitionally equal form `(A.loc p).ιF (D : F) = _`.

Conclude with `map_intCast _ D`.
-/
theorem intCast_isUnit_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  intro F E _ _ _ _ _ sig A D hD
  have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD
  refine (HeightOneSpectrum.Support.finite (𝓞 F) ((D : F)⁻¹)).subset fun p hp => ?_
  by_contra hs
  apply hp
  have hs' : p.valuation F ((D : F)⁻¹) ≤ 1 := by
    have := hs
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at this
    exact this
  have h1 : p.valuation F (D : F) ≤ 1 := by
    have := p.valuation_le_one (K := F) (D : 𝓞 F)
    simpa using this
  have m1 := ((integers_local A).2.2.1 (D : F) p).2 h1
  have m2 := ((integers_local A).2.2.1 ((D : F)⁻¹) p).2 hs'
  have hne : (A.loc p).ιF (D : F) ≠ 0 := by
    rw [map_ne_zero]; exact hDF
  refine ⟨⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (A.loc p).ιF (D : F) * (A.loc p).ιF ((D : F)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hDF, map_one]
  · apply Subtype.ext
    change (A.loc p).ιF ((D : F)⁻¹) * (A.loc p).ιF (D : F) = 1
    rw [← map_mul, inv_mul_cancel₀ hDF, map_one]
  · change (A.loc p).ιF (D : F) = _
    exact map_intCast _ D

end GlobalTheory.HL.PlacesInt
