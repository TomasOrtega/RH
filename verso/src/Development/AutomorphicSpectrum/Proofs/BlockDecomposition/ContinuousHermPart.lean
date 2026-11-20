import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelic

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermVol

variable (D : D7) (r : ℕ)

def hermPart (x : Mx D r r) : Mx D r r := half D • (x + adj x)

variable {D r}

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem hermPart_mem (x : Mx D r r) : hermPart D r x ∈ hermA D r := by
  change adj (hermPart D r x) = hermPart D r x
  rw [hermPart, adj_smul, cA_half, adj_add, adj_adj, add_comm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem hermPart_of_mem {c : Mx D r r} (hc : c ∈ hermA D r) : hermPart D r c = c := by
  have h : adj c = c := hc
  rw [hermPart, h, smul_add, half_smul_add]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hermPart_add (x y : Mx D r r) : hermPart D r (x + y) = hermPart D r x + hermPart D r y := by
  rw [hermPart, hermPart, hermPart, adj_add, add_add_add_comm, smul_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem hermPart_rat {x : Mx D r r} (hx : x ∈ ratMx D r r) : hermPart D r x ∈ ratMx D r r := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ + γᴴ), ?_⟩
  rw [rat_smul, rat_add, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_hermPart : Continuous (hermPart D r) :=
  haveI : IsTopologicalAddGroup (Mx D r r) := (lattice_Mx D r r).1
  show Continuous fun x => half D • (x + adj x) from (continuous_id.add continuous_adj).const_smul (half D)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isClosed_hermA : IsClosed (hermA D r : Set (Mx D r r)) :=
  haveI : T2Space (Mx D r r) := (lattice_Mx D r r).2.2.2.1
  isClosed_eq continuous_adj continuous_id

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCoLat_herm : GlobalTheory.CuspGeneric.IsCoLat (ratHerm D r) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D r r
  refine ⟨?_, ?_⟩
  · let φ : ratHerm D r → ratMx D r r := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D r r → hermA D r := fun x => ⟨hermPart D r x, hermPart_mem x⟩
    have hP : Continuous P := continuous_hermPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_comap.2 (hermPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change hermPart D r (γ + x.1) = hermPart D r γ + x.1
    rw [hermPart_add, hermPart_of_mem x.2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_isCovolOneH : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖 := by
  intro D r
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) := (isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (hermA D r) _ isCoLat_herm
  exact ⟨μ, 𝓕, hμ, hF, h1⟩

end GlobalTheory.CompanionTheory.HermVol
