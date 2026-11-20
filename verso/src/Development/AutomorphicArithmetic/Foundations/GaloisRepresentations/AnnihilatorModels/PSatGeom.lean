import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem coe_bind (B : Multiset ℂˣ) :
    (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
  show B.bind (fun b => {(b : ℂ)}) = _
  exact Multiset.bind_singleton B _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.satGeom_of :
    SatGeom := by
  intro E Ω _ _ _ _ _ A w h a B
  have h0 : (0 : ℂ) ∉ B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)) := by
    simp
  refine ⟨?_, ?_⟩
  · show ((WD.lpUnr h _).lpTw _).unr
    rw [WD.unr_tw]
    exact (WD.lpUnr_spec _ h0).1
  intro g hg
  show ((WD.lpUnr h _).lpTw _).charPol g = _
  unfold WD.lpUnr
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hg, coe_bind]
  have hsm : ∀ (s : ℂ) {ι : Type} (f : ι → ℂ), s • diagEnd f = diagEnd (fun i => s * f i) := by
    intro s ι f
    ext v i
    simp [diagEnd, mul_assoc]
  rw [hsm, charpoly_diagEnd, Finset.prod_eq_multiset_prod]
  set s : ℂ := (↑(normV w) ^ (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) with hs
  refine (congrArg Multiset.prod (Multiset.map_univ (B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)))
    (fun x => Polynomial.X - Polynomial.C (s * ↑(WD.unitOf x) ^ (-1 : ℤ))))).trans ?_
  unfold rootPol
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro b _
  simp only [Function.comp_apply]
  have hs' : s = (normV w : ℂ) ^ (((a : ℂ) - 1) / 2) := by
    rw [hs, zpow_neg_one, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [WD.coe_unitOf (Units.ne_zero _), Units.val_inv_eq_inv_val, zpow_neg_one, inv_inv, hs']
