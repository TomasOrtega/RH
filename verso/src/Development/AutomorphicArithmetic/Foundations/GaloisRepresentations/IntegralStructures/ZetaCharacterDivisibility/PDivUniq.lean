import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `hD E Ω _ _ _ _ _ _ l _ ι a d hd U hU r r' hr hr'`. Take `⟨hc, hs, V, X, hVo, hVd, h⟩` from `hr`. Take `⟨hc', hs', V', X', hVo', hVd', h'⟩` from `hr'`. Establish `hS` using `hD E Ω l a d hd U hU (X ∪ X')`. Establish `hI` using `(hS.inter_of_isOpen_right hVd hVo).inter_of_isOpen_right hVd' hVo'`.

Use `GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _ (hI.preimage (Homeomorph.inv (G E Ω)).isOpenMap) ?_` and prove the remaining obligations. Introduce and unpack `g ⟨⟨⟨w, hw, hus, hl, ⟨B, hB⟩, A, hP, hF⟩, hV⟩, hV'⟩`. Establish `hwX : w ∉ X` using `fun hx => hw (Finset.mem_union_left _ hx)`. Establish `hwX' : w ∉ X'` using `fun hx => hw (Finset.mem_union_right _ hx)`. Establish `e1` using `(h w hwX hus hl B hB A hP).2 g⁻¹ hF hV`.

Establish `e2` using `(h' w hwX' hus hl B hB A hP).2 g⁻¹ hF hV'`. Rewrite `e1`, `e2` using `[inv_inv]`. Conclude with `Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)`.
-/
theorem UpperTheory.Gal.Int.Div.divUniq_of :
    DenseUs → DivUniq := by
  classical
  intro hD E Ω _ _ _ _ _ _ l _ ι a d hd U hU r r' hr hr'
  obtain ⟨hc, hs, V, X, hVo, hVd, h⟩ := hr
  obtain ⟨hc', hs', V', X', hVo', hVd', h'⟩ := hr'
  have hS := hD E Ω l a d hd U hU (X ∪ X')
  have hI := (hS.inter_of_isOpen_right hVd hVo).inter_of_isOpen_right hVd' hVo'
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _
    (hI.preimage (Homeomorph.inv (G E Ω)).isOpenMap) ?_
  rintro g ⟨⟨⟨w, hw, hus, hl, ⟨B, hB⟩, A, hP, hF⟩, hV⟩, hV'⟩
  have hwX : w ∉ X := fun hx => hw (Finset.mem_union_left _ hx)
  have hwX' : w ∉ X' := fun hx => hw (Finset.mem_union_right _ hx)
  have e1 := (h w hwX hus hl B hB A hP).2 g⁻¹ hF hV
  have e2 := (h' w hwX' hus hl B hB A hP).2 g⁻¹ hF hV'
  rw [inv_inv] at e1 e2
  exact Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
