import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlatStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Pad

section Sums

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem expo_finsetSum {ι : Type} (t : Finset ι) (w : ι → (Sym E →₀ ℤ)) :
    expo Dw (∑ i ∈ t, w i) = ∑ i ∈ t, expo Dw (w i) := by
  funext z
  rw [Finset.sum_apply]
  unfold expo
  exact (Finsupp.sum_finsetSum_index (fun _ => by simp) fun _ _ _ => by split_ifs <;> simp).symm

end Sums

end GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem divOf_finsetSum (k : s.Comp) {ι : Type} (t : Finset ι) (n : ι → Letter S.Dw → ℤ) :
    divOf (Φ.C k) (∑ i ∈ t, n i) = ∑ i ∈ t, divOf (Φ.C k) (n i) := by
  unfold divOf
  simp only [Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem sum_rootExp (τ : D.what₂.Tau) :
    ∑ i : Fin N, rootExp S (τ, i) = expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ)) := by
  rw [detSym, expo_finsetSum, S.rank_eq, Finset.sum_range]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sum_divOf_rootExp_eq_principal (k : s.Comp) (τ : D.what₂.Tau) :
    ∃ g, ∑ i : Fin N, divOf (Φ.C k) (rootExp S (τ, i)) = CartierDiv.principal g := by
  have hf := GlobalTheory.T.flat_section_isFlat D A N j S κ s Φ k τ
  rw [← divOf_finsetSum, sum_rootExp]
  have h0 : flatSec s Φ k τ ≠ 0 := (hf (genericPoint _)).ne_zero
  refine ⟨(Units.mk0 _ h0)⁻¹, CartierDiv.ext_of_isEqn fun x => ⟨(Units.mk0 _ h0)⁻¹, ?_, CartierDiv.isEqn_principal _ x⟩⟩
  rw [CartierDiv.isEqn_iff_generatesAt_inv, Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]
  exact hf x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toPic_sum_divOf_rootExp : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag)
    (k : s.Comp) (τ : D.what₂.Tau), toPic (∑ i : Fin N, divOf (Φ.C k) (rootExp S (τ, i))) = 0 := by
  intro D A N j S κ s Φ k τ
  obtain ⟨g, hg⟩ := sum_divOf_rootExp_eq_principal Φ k τ
  rw [hg]
  exact toPic_principal g

end GlobalTheory.ShFam
