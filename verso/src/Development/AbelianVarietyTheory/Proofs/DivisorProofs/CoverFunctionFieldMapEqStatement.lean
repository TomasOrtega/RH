import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mean4O.Cover.φ_eq_fnMap` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoverFunctionFieldMapEq.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cover_function_field_map_eq : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y), ∃ hη : V.π (genericPoint V.G) ⤳ genericPoint Y.X, V.φ = GlobalTheory.TrueGeo.SmallSec.fnMap V.π hη := by
  first | exact @GlobalTheory.Mean4O.Cover.φ_eq_fnMap | exact GlobalTheory.Mean4O.Cover.φ_eq_fnMap | (intros; apply GlobalTheory.Mean4O.Cover.φ_eq_fnMap <;> assumption)
