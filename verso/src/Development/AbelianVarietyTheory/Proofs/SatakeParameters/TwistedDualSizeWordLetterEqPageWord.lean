import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Introduce `D L C j ε τ ψ hR a`. Establish `hB` using `GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ ψ hR`. Establish `hpos : (etaHat L : ℤ) < szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))` using `hB.2.2.2.2.2 a`. Establish `h0 : 0 ≤ szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))` using `by omega`. Establish `hc : ((szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat : ℤ) = szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))` using `Int.toNat_of_nonneg h0`.

Establish `hS : (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) + (sHat L : ℤ)).toNat = (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat + sHat L` using `by omega`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hc`. Simplify using `only [recWord, pageWord, WordData.Mi, hS]`. Simplify using `only [recWord, pageWord, WordData.hi, hS]`.

Simplify using `only [ThickN, recWord, pageWord, WordData.thick]`. Use linear arithmetic over natural numbers and integers.
-/
theorem recWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG),
    Roomy L C → ∀ a : ZMod (orderOf ψ),
    (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧
    (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧
    (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧
    (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  intro D L C j ε τ ψ hR a
  have hB := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ ψ hR
  have hpos : (etaHat L : ℤ) < szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := hB.2.2.2.2.2 a
  have h0 : 0 ≤ szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := by omega
  have hc : ((szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat : ℤ) =
      szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := Int.toNat_of_nonneg h0
  have hS : (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) + (sHat L : ℤ)).toNat =
      (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat + sHat L := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hc
  · simp only [recWord, pageWord, WordData.Mi, hS]
  · simp only [recWord, pageWord, WordData.hi, hS]
  · simp only [ThickN, recWord, pageWord, WordData.thick]
    omega

end GlobalTheory.HTW.Rec
