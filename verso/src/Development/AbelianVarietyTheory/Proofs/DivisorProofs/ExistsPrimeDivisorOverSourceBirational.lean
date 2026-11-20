import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

/- English proof (translation)
Introduce `k _ X Y _ _ p s _ hs E`. Set `e : X.functionField ≃+* Y.functionField` to `RingEquiv.ofBijective (functionFieldMap s) hs`. Set `V : ValuationSubring Y.functionField` to `E.ring.comap e.symm.toRingHom`. Establish `hV (f : X.functionField) : f ∈ E.ring ↔ functionFieldMap s f ∈ V`. Express the relevant statement in the definitionally equal form `f ∈ E.ring ↔ e.symm (e f) ∈ E.ring`.

Rewrite using `[e.symm_apply_apply]`. Set `φ : E.ring →+* V` to `((functionFieldMap s).comp E.ring.subtype).codRestrict V fun a => (hV _).1 a.2`. Establish `hφ : Function.Bijective φ` using `⟨fun _ _ h => Subtype.ext (hs.1 (congrArg Subtype.val h)), fun f => ⟨⟨e.symm f.1, f.2⟩, Subtype.ext (e.apply_symm_apply f.1)⟩⟩`. Establish `hc (a : k) : functionFieldMap s (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a` using `RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s) a`. Use `⟨⟨V, fun a => hc a ▸ (hV _).1 (E.const_mem a), IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (RingEquiv.ofBijective φ hφ), ?_⟩, hV⟩` and prove the remaining obligations.

Establish `h3` using `E.essFiniteType.comp (RingHom.FiniteType.of_surjective φ hφ.2).essFiniteType`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext fun a => Subtype.ext (hc a).symm`.
-/
theorem DivOver.exists_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hs E
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hs
  let V : ValuationSubring Y.functionField := E.ring.comap e.symm.toRingHom
  have hV (f : X.functionField) : f ∈ E.ring ↔ functionFieldMap s f ∈ V := by
    change f ∈ E.ring ↔ e.symm (e f) ∈ E.ring
    rw [e.symm_apply_apply]
  let φ : E.ring →+* V :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict V fun a => (hV _).1 a.2
  have hφ : Function.Bijective φ :=
    ⟨fun _ _ h => Subtype.ext (hs.1 (congrArg Subtype.val h)),
      fun f => ⟨⟨e.symm f.1, f.2⟩, Subtype.ext (e.apply_symm_apply f.1)⟩⟩
  have hc (a : k) : functionFieldMap s (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a :=
    RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s) a
  refine ⟨⟨V, fun a => hc a ▸ (hV _).1 (E.const_mem a),
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective φ hφ), ?_⟩, hV⟩
  have h3 := E.essFiniteType.comp (RingHom.FiniteType.of_surjective φ hφ.2).essFiniteType
  convert h3 using 1
  exact RingHom.ext fun a => Subtype.ext (hc a).symm

end GlobalTheory.Discrepancy
