import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIsoSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdelicIsoSymm.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.adelic_iso_symm : ∀ (F : Type) [Field F] [NumberField F] (C : GlobalTheory.TrueGeo.CxSt F) (Y Y' : Var F) (A : GlobalTheory.TrueGeo.Adl C Y) (A' : GlobalTheory.TrueGeo.Adl C Y') (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ), AdlIso A A' φ ψ u → ∃ (ψ' : Y.Fn →+* Y'.Fn) (u' : Y'.Fnˣ), AdlIso A' A φ.symm ψ' u' := by
  first | exact @GlobalTheory.ShFam.GalCarry.Symm.adlIso_symm | exact GlobalTheory.ShFam.GalCarry.Symm.adlIso_symm | (intros; apply GlobalTheory.ShFam.GalCarry.Symm.adlIso_symm <;> assumption)
