import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vert.Model.Hom

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : GlobalTheory.Vert.Model O}
  (f : GlobalTheory.Vert.Model.Hom B' B)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem fibreDeg_one_eq_ite : f.fibreDeg 1 =
    if 0 = f.relDim then (chi f.fnField (structureModule f.genFibre) : ℚ) else 0 := by
  have h := f.fibreDeg_prod (ι := Fin 0) (L := finZeroElim) finZeroElim
  simp only [Finset.univ_eq_empty, Finset.prod_empty, Fintype.card_fin] at h
  rw [h, interNum_of_isEmpty]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compactSpace_genFibre : CompactSpace f.genFibre :=
  QuasiCompact.compactSpace_of_compactSpace f.genFibreStr

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isNoetherian_genFibre : AlgebraicGeometry.IsNoetherian f.genFibre :=
  have := f.compactSpace_genFibre
  isNoetherian_of_locallyOfFiniteType_field f.genFibreStr

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem suppDim_genFibre_le_zero (hr : f.relDim = 0) :
    suppDim (structureModule f.genFibre) ≤ 0 := by
  have h := suppDim_structureModule.trans_le f.dim_genFibre_le
  rw [hr] at h
  exact_mod_cast h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hdim_zero_genFibre : hdim f.fnField (structureModule f.genFibre) 0 =
    Module.finrank f.fnField Γ(f.genFibre, ⊤) :=
  ((coh.zeroUnitEquiv f.genFibre).restrictScalars f.fnField).finrank_eq

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finite_Γ_genFibre (hr : f.relDim = 0) : Module.Finite f.fnField Γ(f.genFibre, ⊤) := by
  have := f.compactSpace_genFibre
  have := (finiteCohTwists_of_suppDim_le_zero f.genFibreStr
    (f.suppDim_genFibre_le_zero hr)).finiteCoh.finite 0
  exact Module.Finite.equiv ((coh.zeroUnitEquiv f.genFibre).restrictScalars f.fnField)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nontrivial_Γ_genFibre : Nontrivial Γ(f.genFibre, ⊤) :=
  have : Nonempty (⊤ : f.genFibre.Opens) := ⟨⟨Classical.arbitrary f.genFibre, trivial⟩⟩
  Scheme.component_nontrivial f.genFibre ⊤

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem fibreDeg_one_of_relDim_eq_zero (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B)
    (hr : f.relDim = 0) :
    0 < Module.finrank f.fnField Γ(f.genFibre, ⊤) ∧
      f.fibreDeg 1 = (Module.finrank f.fnField Γ(f.genFibre, ⊤) : ℚ) := by
  have := f.isNoetherian_genFibre
  have := f.finite_Γ_genFibre hr
  have := f.nontrivial_Γ_genFibre
  refine ⟨Module.finrank_pos, ?_⟩
  rw [f.fibreDeg_one_eq_ite, if_pos hr.symm,
    chi_eq_hdim_zero_of_suppDim_le_zero f.fnField (f.suppDim_genFibre_le_zero hr),
    f.hdim_zero_genFibre]
  push_cast
  rfl

end GlobalTheory.Vert.Model.Hom
